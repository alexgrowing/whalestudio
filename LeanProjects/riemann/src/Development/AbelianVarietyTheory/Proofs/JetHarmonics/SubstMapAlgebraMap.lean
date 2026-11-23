import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HasSubstAddSqZero
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsToJetEq
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsNilpotentOfMemKerJetTruncR
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.JetSer
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε LPow ThetaGrp IsActOf WeilIs translT GlobalFnsSt)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Good val sval gs)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDer

variable {R : Type} [CommRing R]

theorem exists_jet_factor {κ A : Type} [Finite κ] [CommRing A] [Algebra R A] (T : MvPowerSeries κ R →ₐ[R] A)
    (hT : ∀ p, IsNilpotent (T (X p))) :
    ∃ (n : ℕ) (Θ : JetR R κ (n + 1) →ₐ[R] A), ∀ g, Θ (toJet (n + 1) g) = T g := by
  let J : Ideal A := Ideal.span (Set.range fun p => T (X p))
  have hfg : J.FG := Submodule.fg_span (Set.finite_range _)
  have hn : IsNilpotent J := (Ideal.FG.isNilpotent_iff_le_nilradical hfg).2 (by
    rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    exact hT p)
  obtain ⟨n, hn⟩ := hn
  have hJ : J ^ (n + 1 + 1) = ⊥ := by
    rw [add_assoc, pow_add, hn, zero_mul, Ideal.zero_eq_bot]
  have hm : ∀ p, T (X p) ∈ J := fun p => Ideal.subset_span ⟨p, rfl⟩
  refine ⟨n, jetLift R J hJ (fun p => T (X p)) hm, fun g => ?_⟩
  have h := GlobalTheory.algHom_sub_aeval_truncTotal_mem T hm (n + 1 + 1) g
  rw [hJ, Ideal.mem_bot, sub_eq_zero] at h
  exact h.symm

theorem exists_trunc_one {G : Over (Spec (CommRingCat.of R))} {κ : Type} (x : Fam G κ)
    (hx : ∀ m, spMap (jetTruncR R κ m) ≫ x (m + 1) = x m) (n : ℕ) :
    ∃ t : JetR R κ (n + 1) →ₐ[R] JetR R κ 1, (∀ j, t (zR (n + 1) j) = zR 1 j) ∧ spMap t ≫ x (n + 1) = x 1 := by
  induction n with
  | zero =>
    refine ⟨AlgHom.id R _, fun _ => rfl, ?_⟩
    have : spMap (R₀ := R) (AlgHom.id R (JetR R κ 1)) = 𝟙 _ := by
      apply Over.OverMorphism.ext
      rw [spMap_left]
      exact Spec.map_id _
    rw [this, Category.id_comp]
  | succ n ih =>
    obtain ⟨t, h1, h2⟩ := ih
    refine ⟨t.comp (jetTruncR R κ (n + 1)), fun j => h1 j, ?_⟩
    rw [← spMap_comp, Category.assoc, hx, h2]

theorem subst_map_algebraMap {σ τ S : Type} [Finite σ] [CommRing S] [Algebra R S] {a : σ → MvPowerSeries τ S}
    (ha : HasSubst a) (f : MvPowerSeries σ R) :
    subst a (MvPowerSeries.map (algebraMap R S) f) = subst a f := by
  rw [map_algebraMap_eq_subst_X, subst_comp_subst_apply HasSubst.X ha]
  congr 1
  funext s
  exact subst_X ha s

def tanPair (d : ℕ) (v : Fin d → R) : Fin 2 × Fin d → PS (DualNumber R) 1 d := fun p =>
  (![pt (DualNumber R) d 0, fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R)] :
    Fin 2 → Pt (DualNumber R) 1 d) p.1 p.2

theorem inr_nilpotent (r : R) : IsNilpotent (TrivSqZeroExt.inr r : DualNumber R) :=
  ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩

theorem hasSubst_tanPair (d : ℕ) (v : Fin d → R) : HasSubst (tanPair d v) := by
  apply hasSubst_of_constantCoeff_nilpotent
  rintro ⟨j, i⟩
  fin_cases j
  · simp [tanPair, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · simpa [tanPair] using inr_nilpotent (v i)

theorem ev_pt_pt {d : ℕ} (g : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] g = g := by
  have : (fun p : Fin 2 × Fin d => (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) p.1 p.2) = X := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j <;> rfl
  unfold ev
  rw [this, subst_self, id]

theorem subst_tanPair_fst {d : ℕ} (v : Fin d → R) (f : PS R 1 d) :
    subst (tanPair d v) (ev (n := 2) ![pt R d 0] f) = MvPowerSeries.map (algebraMap R (DualNumber R)) f := by
  have ha : HasSubst (fun p : Fin 1 × Fin d => (![pt R d 0] : Fin 1 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt])
  unfold ev
  rw [subst_comp_subst_apply ha (hasSubst_tanPair d v), map_algebraMap_eq_subst_X]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  exact subst_X (hasSubst_tanPair d v) ((0 : Fin 2), i)

theorem subst_tanPair_add {d : ℕ} (Gl : FGLaw R d) (v : Fin d → R) (f : PS R 1 d) :
    subst (tanPair d v) (ev (n := 2) ![addOf Gl.F (pt R d 0) (pt R d 1)] f) =
      MvPowerSeries.map (algebraMap R (DualNumber R)) f +
        C (DualNumber.eps : DualNumber R) *
          MvPowerSeries.map (algebraMap R (DualNumber R)) (Dof Gl.F v f) := by
  have hF : addOf (n := 2) Gl.F (pt R d 0) (pt R d 1) = Gl.F := funext fun i => ev_pt_pt _
  have ha : HasSubst (fun p : Fin 1 × Fin d => (![Gl.F] : Fin 1 → Pt R 2 d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero (by
      rintro ⟨j, i⟩
      fin_cases j
      exact Gl.const i)
  have e : (fun p : Fin 1 × Fin d => subst (tanPair d v) ((![Gl.F] : Fin 1 → Pt R 2 d) p.1 p.2)) =
      fun p : Fin 1 × Fin d => (![addOf (Gl.mapF (algebraMap R (DualNumber R))) (pt (DualNumber R) d 0)
          (fun i => C (TrivSqZeroExt.inr (v i) : DualNumber R))] : Fin 1 → Pt (DualNumber R) 1 d) p.1 p.2 := by
    funext p
    obtain ⟨j, i⟩ := p
    fin_cases j
    exact (subst_map_algebraMap (hasSubst_tanPair d v) (Gl.F i)).symm
  have hc := ha.comp (hasSubst_tanPair d v)
  simp only [substAlgHom_apply] at hc
  rw [← GlobalTheory.Jets.ev_addOf_eps, hF]
  unfold ev
  rw [subst_comp_subst_apply ha (hasSubst_tanPair d v), ← e, subst_map_algebraMap hc]

theorem dof_eq_of_eigen : JetAlgSt → RepSt → SerSt → ∀ (R : Type) [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (d : ℕ) (x : Fam G (Fin d)), IsUnivChart G d x → ∀ Gl : FGLaw R d, IsLawOf x Gl.F → ∀ (U : G.left.Opens), ⊤ ≤ η[G].left ⁻¹ᵁ U → ∀ (s : Γ(G.left, U)) (f : PS R 1 d), IsSer1 x U s f → ∀ (v : Fin d → R) (y : R) (φ : JetR R (Fin d) 1 →ₐ[R] DualNumber R), (∀ i, φ (zR 1 i) = TrivSqZeroExt.inr (v i)) → (∀ (A : Type) [CommRing A] [Algebra R A] (c : DualNumber R →ₐ[R] A) (r : sp (R₀ := R) A ⟶ G), ⊤ ≤ r.left ⁻¹ᵁ U → ⊤ ≤ (r * (spMap c ≫ spMap φ ≫ x 1)).left ⁻¹ᵁ U → fnVal (r * (spMap c ≫ spMap φ ≫ x 1)).left U s = c (1 + TrivSqZeroExt.inr y) * fnVal r.left U s) → Dof Gl.F v f = C y * f := by
  intro _ hRep _ R _ G _ d x hx Gl hl U _ s f hf v y φ hφ H
  have hb := hasSubst_tanPair d v
  have hpt : ∀ (k : Fin 2) (j : Fin d), constantCoeff (pt R (n := 2) d k j) = 0 := fun k j => by
    simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  obtain ⟨y₁, hy₁, -⟩ := (hRep R G d x hx (Fin 2 × Fin d)).1 (pt R d 0) (hpt 0)
  obtain ⟨y₂, hy₂, -⟩ := (hRep R G d x hx (Fin 2 × Fin d)).1 (pt R d 1) (hpt 1)
  have s₁ := hf 2 _ _ hy₁
  have s₁₂ := hf 2 _ _ (hl.2 2 _ _ _ _ hy₁ hy₂)
  have key : subst (tanPair d v) (ev (n := 2) ![addOf Gl.F (pt R d 0) (pt R d 1)] f) =
      C (1 + TrivSqZeroExt.inr y : DualNumber R) * subst (tanPair d v) (ev (n := 2) ![pt R d 0] f) := by
    refine eq_of_toJet_eq fun m => ?_
    let T : PS R 2 d →ₐ[R] JetR (DualNumber R) (Fin 1 × Fin d) m :=
      ((toJetHom (DualNumber R) (Fin 1 × Fin d) m).restrictScalars R).comp (substAlgHom hb)
    have hT : ∀ g, T g = toJet m (subst (tanPair d v) g) := fun g => by
      rw [← substAlgHom_apply hb]; rfl
    let c : DualNumber R →ₐ[R] JetR (DualNumber R) (Fin 1 × Fin d) m := IsScalarTower.toAlgHom R _ _
    have hc : ∀ a, toJet m (C a : PS (DualNumber R) 1 d) = c a := fun a =>
      (toJetHom (DualNumber R) (Fin 1 × Fin d) m).commutes a
    have hT1 : ∀ i, T (X ((1 : Fin 2), i)) = c (TrivSqZeroExt.inr (v i)) := fun i => by
      rw [hT, subst_X hb, ← hc]; rfl
    have hT0 : ∀ i, T (X ((0 : Fin 2), i)) = zR m ((0 : Fin 1), i) := fun i => by
      rw [hT, subst_X hb, ← toJet_X]; rfl
    obtain ⟨n, Θ, hΘ⟩ := exists_jet_factor T (by
      rintro ⟨j, i⟩
      fin_cases j
      · refine hT0 i ▸ ⟨m + 1, ?_⟩
        have := Ideal.pow_mem_pow (zR_mem_ker (R := DualNumber R) m ((0 : Fin 1), i)) (m + 1)
        rwa [ker_jetAug_pow, Ideal.mem_bot] at this
      · exact hT1 i ▸ (inr_nilpotent (v i)).map c)
    obtain ⟨t, ht, htx⟩ := exists_trunc_one x hx.1 n
    obtain ⟨ψ, hψ, hψy⟩ := hy₂.2 (n + 1)
    have e₂ : spMap c ≫ spMap φ ≫ x 1 = spMap Θ ≫ y₂ (n + 1) := by
      have : c.comp (φ.comp t) = Θ.comp ψ := jet_ext fun j => by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, ht, hφ, hψ, hΘ]
        exact (hT1 j).symm
      rw [hψy, ← htx, ← Category.assoc (spMap φ), spMap_comp, ← Category.assoc, spMap_comp, this,
        ← Category.assoc, spMap_comp]
    have e : (spMap Θ ≫ y₁ (n + 1)) * (spMap c ≫ spMap φ ≫ x 1) = spMap Θ ≫ (y₁ (n + 1) * y₂ (n + 1)) := by
      rw [e₂, MonObj.comp_mul]
    have h := H _ c (spMap Θ ≫ y₁ (n + 1)) (top_le_preimage_comp _ _ U (s₁ (n + 1)).1)
      (by rw [e]; exact top_le_preimage_comp _ _ U (s₁₂ (n + 1)).1)
    have v₁ := fnVal_specMap Θ.toRingHom _ U (s₁ (n + 1)).1 s
    have v₁₂ := fnVal_specMap Θ.toRingHom _ U (s₁₂ (n + 1)).1 s
    rw [(s₁ (n + 1)).2] at v₁
    rw [(s₁₂ (n + 1)).2] at v₁₂
    rw [e] at h
    have h' := v₁₂.symm.trans (h.trans (congrArg (c (1 + TrivSqZeroExt.inr y) * ·) v₁))
    rw [← toJetHom_apply m (C _ * _), map_mul, toJetHom_apply, toJetHom_apply, hc, ← hT, ← hT, ← hΘ, ← hΘ]
    exact h'
  rw [subst_tanPair_add, subst_tanPair_fst] at key
  ext e
  have := congrArg (fun g => TrivSqZeroExt.snd (coeff e g)) key
  simp only [map_add (coeff e), coeff_C_mul, coeff_map] at this
  simpa [TrivSqZeroExt.algebraMap_eq_inl] using this

end GlobalTheory.EigenDer
