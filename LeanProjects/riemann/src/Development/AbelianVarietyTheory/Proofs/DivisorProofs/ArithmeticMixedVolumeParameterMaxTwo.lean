import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.BasicNotions.DV

open MvPolynomial Formalism.BasicNotions.DV

namespace GlobalTheory.ShFam.ParamTwo

open GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo

theorem numL_rename {A B : Type} (num : Multiset B → ℝ) (d : ℕ) (f : A → B) (P : MvPolynomial A ℝ) :
    numL num d (MvPolynomial.rename f P) = numL (fun M => num (M.map f)) d P := by
  classical
  have key : (numL num d).comp (MvPolynomial.rename f).toLinearMap = numL (fun M => num (M.map f)) d := by
    refine (MvPolynomial.basisMonomials A ℝ).ext fun m => ?_
    have hdeg : (Finsupp.mapDomain f m).degree = m.degree := Finsupp.degree_mapDomain f m
    have hb : (MvPolynomial.monomial (Finsupp.mapDomain f m) (1 : ℝ)) =
        MvPolynomial.basisMonomials B ℝ (Finsupp.mapDomain f m) := by
      simp [MvPolynomial.coe_basisMonomials]
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, MvPolynomial.coe_basisMonomials,
      MvPolynomial.rename_monomial, hb, numL, numL, Module.Basis.constr_basis, ← MvPolynomial.coe_basisMonomials,
      Module.Basis.constr_basis, hdeg, Finsupp.toMultiset_map]
  exact congrArg (fun L => L P) key

theorem numL_congr_supported {A : Type} (num num' : Multiset A → ℝ) (d : ℕ) (s : Set A)
    (h : ∀ M : Multiset A, (∀ a ∈ M, a ∈ s) → num M = num' M) (P : MvPolynomial A ℝ)
    (hP : P ∈ MvPolynomial.supported ℝ s) : numL num d P = numL num' d P := by
  classical
  rw [P.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h2 : MvPolynomial.monomial m (P.coeff m) = P.coeff m • MvPolynomial.basisMonomials A ℝ m := by
    simp [MvPolynomial.smul_monomial]
  rw [h2, map_smul, map_smul, numL, numL, Module.Basis.constr_basis, Module.Basis.constr_basis]
  congr 1
  split_ifs
  · refine h _ fun a ha => ?_
    have hv : a ∈ P.vars := (MvPolynomial.mem_vars a).2 ⟨m, hm, (Finsupp.mem_toMultiset _ _).1 ha⟩
    exact (MvPolynomial.mem_supported.1 hP) hv
  · rfl

theorem powerset_map {α β : Type} (f : α → β) (s : Multiset α) :
    (s.map f).powerset = s.powerset.map (Multiset.map f) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.powerset_cons, ih, Multiset.map_map]

theorem polar_map {A B : Type} [AddCommMonoid A] [AddCommMonoid B] (top : A → ℝ) (top' : B → ℝ) (f : A →+ B)
    (M : Multiset A) (h : ∀ T ≤ M, top' (f T.sum) = top T.sum) :
    polar top' (M.map f) = polar top M := by
  unfold polar
  rw [Multiset.card_map, powerset_map, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun T hT => ?_
  simp only [Function.comp, Multiset.card_map]
  rw [← map_multiset_sum, h T (Multiset.mem_powerset.1 hT)]

theorem support_sum {A : Type} (P : A → Prop) (T : Multiset (A →₀ ℤ)) (h : ∀ w ∈ T, ∀ b ∈ w.support, P b) :
    ∀ b ∈ T.sum.support, P b := by
  induction T using Multiset.induction_on with
  | empty => simp
  | cons w T ih =>
    intro b hb
    rw [Multiset.sum_cons] at hb
    rcases Finset.mem_union.1 (Finsupp.support_add hb) with h1 | h1
    · exact h w (Multiset.mem_cons_self _ _) b h1
    · exact ih (fun w' hw' => h w' (Multiset.mem_cons_of_mem hw')) b h1

def lift2 {E : Type} [Field E] (a : Sym E) : Sym E := (a.1, a.2.1.map (max · 2), a.2.2)

def HasPar {E : Type} [Field E] (R : ℝ) (w : Sym E →₀ ℤ) : Prop := ∀ b ∈ w.support, b.2.1 = some R

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem expo_lift2 (w : Sym E →₀ ℤ) : expo Dw (w.mapDomain lift2) = expo Dw w := by
  funext z
  unfold expo
  rw [Finsupp.sum_mapDomain_index (by intro; simp) (by intros; split_ifs <;> simp)]
  rfl

theorem parOf_of_hasPar {R : ℝ} {w : Sym E →₀ ℤ} (h : HasPar R w) (hw : w ≠ 0) : parOf w = some R := by
  have hn : w.support.Nonempty := Finsupp.support_nonempty_iff.2 hw
  unfold parOf
  rw [dif_pos hn]
  exact h _ hn.choose_spec

theorem hasPar_lift2 {R : ℝ} {w : Sym E →₀ ℤ} (h : HasPar R w) : HasPar (max R 2) (w.mapDomain lift2) := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
  simp [lift2, h a ha]

theorem lift_two_ne_zero {R : ℝ} {w : Sym E →₀ ℤ} (h : HasPar R w) (hw : w ≠ 0) : w.mapDomain lift2 ≠ 0 := by
  classical
  have hinj : Set.InjOn lift2 (w.support : Set (Sym E)) := by
    intro a ha b hb e
    have e1 := congrArg Prod.fst e
    have e3 := congrArg (fun t : Sym E => t.2.2) e
    have hab : a.2.1 = b.2.1 := (h a ha).trans (h b hb).symm
    exact Prod.ext e1 (Prod.ext hab e3)
  rw [← Finsupp.support_nonempty_iff, Finsupp.mapDomain_support_of_injOn w hinj, Finset.image_nonempty]
  exact Finsupp.support_nonempty_iff.2 hw

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem lgOf_lift2 (w : Sym E →₀ ℤ) : lgOf Y (w.mapDomain lift2) = lgOf Y w := by
  funext v ε y
  unfold lgOf
  split_ifs with hp
  · dsimp only
    rw [expo_lift2, Finsupp.sum_mapDomain_index (by intro; simp) (by intros; push_cast; ring)]
    rfl
  · rfl

theorem adlOf_lift2 {C : CxSt F} (hm : Mets Y C) (w : Sym E →₀ ℤ) (hp : hm (parOf (w.mapDomain lift2)) = hm (parOf w)) :
    adlOf Y hm (w.mapDomain lift2) = adlOf Y hm w := by
  unfold adlOf
  rw [hp, lgOf_lift2, expo_lift2]

theorem arTop_lift2 {C : CxSt F} (hm : Mets Y C) {R : ℝ} (hR : hm (some (max R 2)) = hm (some R))
    {w : Sym E →₀ ℤ} (h : HasPar R w) : (adlOf Y hm (w.mapDomain lift2)).arTop = (adlOf Y hm w).arTop := by
  by_cases hw : w = 0
  · subst hw; rw [Finsupp.mapDomain_zero]
  · rw [adlOf_lift2 Y hm w (by rw [parOf_of_hasPar h hw, parOf_of_hasPar (hasPar_lift2 h) (lift_two_ne_zero h hw), hR])]

theorem hasPar_rootSym (a : ℕ → Bool) (R : ℝ) (τ : E →+* ℂ) (i : ℕ) : HasPar R (rootSym Dw a (some R) τ i) := by
  intro b hb
  unfold rootSym at hb
  split_ifs at hb <;>
    · have := Finsupp.support_single_subset hb
      rw [Finset.mem_singleton] at this
      subst this
      rfl

theorem lift_two_root_symbol (a : ℕ → Bool) (R : ℝ) (τ : E →+* ℂ) (i : ℕ) :
    (rootSym Dw a (some R) τ i).mapDomain lift2 = rootSym Dw a (some (max R 2)) τ i := by
  unfold rootSym
  split_ifs <;> simp only [Finsupp.mapDomain_single] <;> rfl

end Free

theorem hasPar_wholeSym {E : Type} [Field E] (a : ℕ → Bool) (R : ℝ) {g : ℕ} (k : Fin g ⊕ Fin g) :
    HasPar R (wholeSym (E := E) a (some R) k) := by
  intro b hb
  cases k <;>
    · have := Finsupp.support_single_subset hb
      rw [Finset.mem_singleton] at this
      subst this
      rfl

theorem lift_two_whole_symbol {E : Type} [Field E] (a : ℕ → Bool) (R : ℝ) {g : ℕ} (k : Fin g ⊕ Fin g) :
    (wholeSym (E := E) a (some R) k).mapDomain lift2 = wholeSym a (some (max R 2)) k := by
  cases k <;> simp only [wholeSym, Finsupp.mapDomain_single] <;> rfl

end GlobalTheory.ShFam.ParamTwo

namespace GlobalTheory.ShFam.ParamTwo

open GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo

section FinalTheorems

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

noncomputable def mixE (Sx : Finset ℕ) (R : ℝ) (p : ℕ) : MvPolynomial (Vm D.what₂.Tau N) ℝ →ₐ[ℝ] MvPolynomial (Sym D.host.E →₀ ℤ) ℝ :=
  MvPolynomial.aeval fun v => match v with
    | Sum.inl (b, x) => MvPolynomial.X (rootSym S.Dw (Function.update (ArIn.ind Sx) p b) (some R) (tauEmb D x.1) x.2)
    | Sum.inr (b, k) => MvPolynomial.C ((k.factorial : ℝ)⁻¹) *
        ∑ l : Fin (D.R.f * N) ⊕ Fin (D.R.f * N), MvPolynomial.X (wholeSym (Function.update (ArIn.ind Sx) p b) (some R) l) ^ k

theorem mixE_max (Sx : Finset ℕ) (R : ℝ) (p : ℕ) :
    mixE (S := S) (N := N) Sx (max R 2) p = (MvPolynomial.rename (Finsupp.mapDomain lift2)).comp (mixE (S := S) Sx R p) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rcases v with ⟨b, x⟩ | ⟨b, m⟩
  · simp only [mixE, MvPolynomial.aeval_X, AlgHom.comp_apply, MvPolynomial.rename_X, lift_two_root_symbol]
  · simp only [mixE, MvPolynomial.aeval_X, AlgHom.comp_apply, map_mul, map_sum, map_pow, MvPolynomial.rename_X,
      MvPolynomial.rename_C, lift_two_whole_symbol]

theorem mixE_supported (Sx : Finset ℕ) (R : ℝ) (p : ℕ) (Q : MvPolynomial (Vm D.what₂.Tau N) ℝ) :
    mixE (S := S) Sx R p Q ∈ MvPolynomial.supported ℝ {w | HasPar R w} := by
  induction Q using MvPolynomial.induction_on with
  | C a => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]; exact Subalgebra.algebraMap_mem _ a
  | add P Q hP hQ => rw [map_add]; exact Subalgebra.add_mem _ hP hQ
  | mul_X P v hP =>
    rw [map_mul]
    refine Subalgebra.mul_mem _ hP ?_
    rcases v with ⟨b, x⟩ | ⟨b, m⟩
    · simp only [mixE, MvPolynomial.aeval_X]
      exact MvPolynomial.X_mem_supported.2 (hasPar_rootSym _ _ _ _)
    · simp only [mixE, MvPolynomial.aeval_X]
      refine Subalgebra.mul_mem _ ?_ (Subalgebra.sum_mem _ fun l _ => Subalgebra.pow_mem _ ?_ _)
      · rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _
      · exact MvPolynomial.X_mem_supported.2 (hasPar_wholeSym _ _ _)

variable (fl : s.Flag) {C : CxSt D.what₂.LL} (hm : ∀ k, Mets (fl.C k) C)

theorem mixEv_eq (Sx : Finset ℕ) (R : ℝ) (p : ℕ) (k : s.Comp) :
    ((arIn s fl hm).mixEv Sx R p k : MvPolynomial (Vm D.what₂.Tau N) ℝ →ₐ[ℝ] MvPolynomial (Sym D.host.E →₀ ℤ) ℝ) =
      mixE (S := S) Sx R p := by
  unfold ArIn.mixEv mixE
  congr 1
  funext v
  rcases v with ⟨b, x⟩ | ⟨b, m⟩
  · rfl
  · rfl

theorem arMix_apply (Sx : Finset ℕ) (R : ℝ) (p : ℕ) (Q : MvPolynomial (Vm D.what₂.Tau N) ℝ) :
    (arIn s fl hm).arMix Sx R p Q = ∑ k, numL (polar fun w => (adlOf (fl.C k) (hm k) w).arTop)
      (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1) (mixE (S := S) Sx R p Q) := by
  rw [ArIn.arMix, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  exact congrArg (fun f : MvPolynomial (Vm D.what₂.Tau N) ℝ →ₐ[ℝ] MvPolynomial (Sym D.host.E →₀ ℤ) ℝ =>
    numL (polar fun w => (adlOf (fl.C k) (hm k) w).arTop) (Formalism.DegreeFormula.dimFl D.what₂.Tau N + 1) (f Q)) (mixEv_eq s fl hm Sx R p k)

theorem arMix_max (hR : ∀ k R, hm k (some (max R 2)) = hm k (some R)) (Sx : Finset ℕ) (R : ℝ) (p : ℕ) :
    (arIn s fl hm).arMix Sx (max R 2) p = (arIn s fl hm).arMix Sx R p := by
  refine LinearMap.ext fun Q => ?_
  rw [arMix_apply, arMix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mixE_max, AlgHom.comp_apply, numL_rename]
  refine numL_congr_supported _ _ _ {w | HasPar R w} (fun M hM => ?_) _ (mixE_supported Sx R p Q)
  change polar (fun w => (adlOf (fl.C k) (hm k) w).arTop) (M.map (Finsupp.mapDomain.addMonoidHom lift2)) =
    polar (fun w => (adlOf (fl.C k) (hm k) w).arTop) M
  refine polar_map _ _ _ M fun T hT => ?_
  rw [Finsupp.mapDomain.addMonoidHom_apply]
  exact arTop_lift2 (fl.C k) (hm k) (hR k R)
    (support_sum _ T fun w hw => hM w (Multiset.mem_of_le hT hw))

end FinalTheorems

theorem metsOf_max {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ} (x : ToroidalCompactificationData s)
    (Φ : s.Flag) (k : s.Comp) (R : ℝ) : metsOf x Φ k (some (max R 2)) = metsOf x Φ k (some R) := by
  have hw : ∀ σ, x.wt σ (max R 2) = x.wt σ R := fun σ => funext fun y => by
    simp only [ToroidalCompactificationData.wt, max_eq_left (le_max_right R 2)]
  funext σ n
  simp only [metsOf, ToroidalCompactificationData.eigMetAt]
  congr 2
  exact hw _

theorem arMix_eq_max_two : ∀ (D : D7) (O : Setup D), O.Core → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ),
    O.Y.arMix Sx R p = O.Y.arMix Sx (max R 2) p := by
  intro D O hO Sx R p
  obtain ⟨x, P, h⟩ := hO
  change (arIn O.s O.Φ O.met.hm).arMix Sx R p = (arIn O.s O.Φ O.met.hm).arMix Sx (max R 2) p
  rw [h.hm_eq]
  exact (arMix_max O.s O.Φ (metsOf x O.Φ) (fun k R => metsOf_max x O.Φ k R) Sx R p).symm

end GlobalTheory.ShFam.ParamTwo
