import Formalism.LocalToGlobal.ProjectiveLattices.CoreProofs
import Formalism.LocalToGlobal.ProjectiveLattices.IntAll
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsOfValILeOne

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open scoped WithZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Dvr

variable {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K'] [Algebra V K']
  [IsFractionRing V K']

theorem mem_range_of_vV_nonneg {x : K'} (h : 0 ≤ vV V x) : x ∈ Set.range (algebraMap V K') := by
  by_cases hx : x = 0
  · exact ⟨0, by simp [hx]⟩
  unfold vV valV at h
  have hx0 : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) x ≠ 0 := by
    simpa using hx
  have hle : HeightOneSpectrum.valuation K' (IsDiscreteValuationRing.maximalIdeal V) x ≤ 1 := by
    rw [← WithZero.exp_log hx0, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  obtain ⟨a, ha⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K' x (fun w => by
    have hw : w = IsDiscreteValuationRing.maximalIdeal V :=
      HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal (w.isPrime.isMaximal w.ne_bot))
    rw [hw]
    exact hle)
  exact ⟨a, ha⟩

end Dvr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

section Open

variable (Xo : Moduli Dw l) (c : Coeff l)

def FrBaseChg : Prop :=
  ∀ (S S' : Type) [Field S] [Field S'] [Algebra c.F S] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (y : FrPt Xo c S),
    ∃ z : FrPt Xo c S', FrMap φ y z

def ReFrame : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
    ∀ (y0 : IntFr Xo c T io) (z : FrPt Xo c T.Fr), z.x = y0.1.x →
      ∃ (t : Ix Dw → T.Frˣ) (y' : IntFr Xo c T io), FrBor t z y'.1

def XoNumPt : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (j : c.F →+* L) (x : Sp L ⟶ Xo.X),
    (letI := j.toAlgebra; x ≫ Xo.s = sOf c L)

end Open

def LocFld : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (j : K →+* L) (la : HeightOneSpectrum (𝓞 K)),
    ∃ (T : CDVR) (k : L →+* T.Fr) (e : ℕ), OverLa la T.V (k.comp j) e ∧ T.FinRes

section Proofs

variable {Xo : Moduli Dw l} {c : Coeff l}

theorem intAll_of (hE : IntFrExt Xo c) (hB : FrBaseChg Xo c) (hR : ReFrame Xo c) : IntAll Xo c := by
  intro la T io e ho hfin y
  let _ := io.toAlgebra
  obtain ⟨T', i, r, hr, hi, hfin', y0, hx0⟩ := hE T io hfin y.x y.x_over
  let _ : Algebra c.F T'.Fr := (i.comp io).toAlgebra
  let φ : T.Fr →ₐ[c.F] T'.Fr := { i with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := hB T.Fr T'.Fr φ y
  obtain ⟨t, y', hb⟩ := hR T' (i.comp io) y0 z (by rw [hz.1, hx0])
  refine ⟨T', i.comp io, r * e, y', ho.bc i hr hi, hfin', φ, z, t, ?_, hz, hb⟩
  intro a
  apply mem_range_of_vV_nonneg
  show 0 ≤ vV T'.V (i (algebraMap T.V T.Fr a))
  rw [hi]
  have h0 : 0 ≤ vV T.V (algebraMap T.V T.Fr a) := by
    by_cases ha : algebraMap T.V T.Fr a = 0
    · rw [ha]; simp [vV]
    · have hv : valV T.V (algebraMap T.V T.Fr a) ≤ 1 :=
        (IsDiscreteValuationRing.maximalIdeal T.V).valuation_le_one a
      have hn := valV_ne_zero (V := T.V) ha
      have := (WithZero.log_le_log hn one_ne_zero).2 hv
      simp only [WithZero.log_one] at this
      simp only [vV]; omega
  exact mul_nonneg (by exact_mod_cast hr.le) h0

theorem algPtLa_of (hN : XoNumPt Xo c) (hL : LocFld) : AlgPtLa Xo c := by
  unfold AlgPtLa
  intro la
  obtain ⟨L, _, _, j, x, hx⟩ := hN
  obtain ⟨T, k, e, hO, hF⟩ := hL c.F L j la
  refine ⟨T, k.comp j, e, hO, hF, spMap k ≫ x, ?_⟩
  unfold sOf at hx ⊢
  rw [Category.assoc, hx]
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem intFrNe_of' (hN : XoNumPt Xo c) (hL : LocFld) (hE : IntFrExt Xo c) : IntFrNe Xo c (algCls Xo c) :=
  intFrNe_of (algPtLa_of hN hL) hE

end Proofs

section Frames

theorem isCombAt_unique {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} {a : Fin m → S}
    {w w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (h : IsCombAt x v a w) (h' : IsCombAt x v a w') : w = w' := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  have huu : u = u' := funext fun i => Over.OverMorphism.ext ((hu i).trans (hu' i).symm)
  rw [huu]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem epsMul_comp_alg {S : Type} [CommRing S] (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
  exact RingHom.ext fun y => by simp [epsMul]

def epsPt {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (a : S) : tEps x ⟶ Xo.univ.t.G :=
  Over.homMk (spMap (epsMul a) ≫ v) (by
    rw [Category.assoc, hv.1, ← Category.assoc, spMap_comp', epsMul_comp_alg]
    rfl)

theorem epsPt_left {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) (a : S) :
    (epsPt hv a).left = spMap (epsMul a) ≫ v :=
  Over.homMk_left _ _

theorem isCombAt_exists {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) (a : Fin m → S) :
    ∃ w, IsCombAt x v a w := ⟨_, fun i => epsPt (hv i) (a i), fun i => epsPt_left (hv i) (a i), rfl⟩

theorem isCombAt_epsPt {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) (a : Fin m → S) :
    IsCombAt x v a ((List.ofFn fun i => epsPt (hv i) (a i)).prod.left) := ⟨fun i => epsPt (hv i) (a i), fun i => epsPt_left (hv i) (a i), rfl⟩

theorem epsPt_zero {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : epsPt hv 0 = 1 := by
  have he : epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    apply RingHom.ext
    intro r
    ext <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  let φ : tEps x ⟶ Over.mk x := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  have h1 : (φ ≫ (1 : Over.mk x ⟶ Xo.univ.t.G)) = 1 := MonObj.comp_one φ
  apply Over.OverMorphism.ext
  rw [← h1]
  simp only [epsPt, Over.homMk_left, Over.comp_left, φ]
  rw [he, ← spMap_comp', Category.assoc, hv.2]

theorem epsPt_one_left {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) : (epsPt hv 1).left = v := by
  rw [epsPt_left]
  have h1 : epsMul (1 : S) = RingHom.id _ := RingHom.ext fun y => by simp [epsMul]
  rw [h1]
  simp [spMap]

private theorem prod_ofFn_single_lemma {M : Type*} [Monoid M] (m : ℕ) :
    ∀ (f : Fin m → M) (j : Fin m), (∀ i, i ≠ j → f i = 1) → (List.ofFn f).prod = f j := by
  induction m with
  | zero => intro f j _; exact j.elim0
  | succ m ih =>
    intro f j h
    rw [List.ofFn_succ, List.prod_cons]
    by_cases hj : j = 0
    · subst hj
      rw [List.prod_eq_one, _root_.mul_one]
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact h _ (Fin.succ_ne_zero i)
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
      rw [h 0 (Fin.succ_ne_zero j').symm, _root_.one_mul]
      exact ih (fun i => f i.succ) j' (fun i hi => h _ (fun he => hi (Fin.succ_injective _ he)))

theorem isCombAt_single {S : Type} [CommRing S] {Xo : Moduli Dw l} {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) (j : Fin m) :
    IsCombAt x v (Pi.single j 1) (v j) := by
  refine ⟨fun i => epsPt (hv i) ((Pi.single j (1 : S) : Fin m → S) i),
    fun i => epsPt_left (hv i) _, ?_⟩
  rw [prod_ofFn_single_lemma m (fun i => epsPt (hv i) ((Pi.single j (1 : S) : Fin m → S) i)) j
    (fun i hi => by
      show epsPt (hv i) ((Pi.single j (1 : S) : Fin m → S) i) = 1
      rw [Pi.single_eq_of_ne hi]
      exact epsPt_zero (hv i))]
  simp only [Pi.single_eq_same]
  exact epsPt_one_left (hv j)

variable (Xo : Moduli Dw l) (c : Coeff l)

def TanLin : Prop :=
  ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)),
    (∀ j, IsTanAt x (v j)) →
      ∀ {m' : ℕ} (w : Fin m' → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (A : Matrix (Fin m) (Fin m') S)
        (N : Fin m' → S) (w' : Sp (DualNumber S) ⟶ Xo.univ.t.G.left),
        (∀ i, IsCombAt x v (fun j => A j i) (w i)) → IsCombAt x w N w' → IsCombAt x v (A.mulVec N) w'

variable {Xo c} in

def SClause {S : Type} [CommRing S] [Algebra c.F S] (a : S) (y y' : FrPt Xo c S) : Prop :=
  ∃ pm : Gx y'.x ⟶ Gx y.x, pm ≫ (snd (Over.mk y.x) Xo.univ.t.G).left = (snd (Over.mk y'.x) Xo.univ.t.G).left ∧
    pm ≫ (fst (Over.mk y.x) Xo.univ.t.G).left = (fst (Over.mk y'.x) Xo.univ.t.G).left ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx y'.x).U i ≤ pm ⁻¹ᵁ (PPx y.x).U i),
      (pm.appLE _ _ h).hom (scal y.x a i * y.s.f i) = y'.s.f i

def IntRebase : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr), letI := io.toAlgebra
    ∀ (y0 : IntFr Xo c T io) (z : FrPt Xo c T.Fr), z.x = y0.1.x →
      ∀ k : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.V, (∀ τ, IsUnit (k τ).det) →
        ∃ (y'' : IntFr Xo c T io) (t0 : T.Frˣ), y''.1.x = z.x ∧
          (∀ τ i, IsCombAt y0.1.x (y0.1.u τ) (fun j => algebraMap T.V T.Fr (k τ j i)) (y''.1.u τ i)) ∧
          SClause (t0 : T.Fr) z y''.1

variable {Xo c}

theorem reFrame_of (hT : TanLin Xo) (hR : IntRebase Xo c) : ReFrame Xo c := by
  intro T io
  let _ := io.toAlgebra
  intro y0 z hx
  have tz : ∀ τ i, IsTanAt y0.1.x (z.u τ i) := fun τ i => by rw [← hx]; exact z.tan τ i
  have ty : ∀ τ i, IsTanAt z.x (y0.1.u τ i) := fun τ i => by rw [hx]; exact y0.1.tan τ i
  have hA : ∀ τ i, ∃ a : Fin (Dw.mult τ) → T.Fr, IsCombAt y0.1.x (y0.1.u τ) a (z.u τ i) :=
    fun τ i => (y0.1.basis τ (z.u τ i) (tz τ i) (z.eig τ i)).exists
  choose a ha using hA
  have hB : ∀ τ j, ∃ b : Fin (Dw.mult τ) → T.Fr, IsCombAt z.x (z.u τ) b (y0.1.u τ j) :=
    fun τ j => (z.basis τ (y0.1.u τ j) (ty τ j) (y0.1.eig τ j)).exists
  choose b hb using hB
  let A : ∀ τ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr := fun τ => Matrix.of fun j i => a τ i j
  let Bm : ∀ τ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) T.Fr := fun τ => Matrix.of fun j i => b τ i j
  have hAB : ∀ τ, A τ * Bm τ = 1 := by
    intro τ
    ext j' i'
    have hb' : IsCombAt y0.1.x (z.u τ) (b τ i') (y0.1.u τ i') := by rw [← hx]; exact hb τ i'
    have hc := hT T.Fr y0.1.x (y0.1.u τ) (y0.1.tan τ) (z.u τ) (A τ) (b τ i') (y0.1.u τ i')
      (fun i => ha τ i) hb'
    have hu := isCombAt_single (y0.1.tan τ) i'
    have heq := (y0.1.basis τ (y0.1.u τ i') (y0.1.tan τ i') (y0.1.eig τ i')).unique hc hu
    have h1 := congrFun heq j'
    simp only [Matrix.mulVec, dotProduct, A, Bm, Matrix.of_apply] at h1
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [A, Bm, Matrix.of_apply]
    rw [h1, Pi.single_apply]
  have hdet : ∀ τ, (A τ).det ≠ 0 := fun τ h => by
    have h2 := congrArg Matrix.det (hAB τ)
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at h2
    exact zero_ne_one h2
  choose k N hk hN hNd hAN using fun τ => iwasawa' (V := T.V) (A τ) (hdet τ)
  obtain ⟨y'', t0, hx'', hu'', hs''⟩ := hR T io y0 z hx k hk
  refine ⟨fun o => Option.casesOn o t0 (fun p => Units.mk0 (N p.1 p.2 p.2) (hNd p.1 p.2)), y'', ?_⟩
  unfold FrBor
  refine ⟨hx'', fun τ i => ?_, hs''⟩
  refine ⟨fun j => N τ j i, rfl, fun j hij => hN τ hij, ?_⟩
  obtain ⟨w', hw'⟩ := isCombAt_exists (z.tan τ) (fun j => N τ j i)
  have hw0 : IsCombAt y0.1.x (z.u τ) (fun j => N τ j i) w' := by rw [← hx]; exact hw'
  have hc := hT T.Fr y0.1.x (y0.1.u τ) (y0.1.tan τ) (z.u τ) (A τ) (fun j => N τ j i) w'
    (fun i => ha τ i) hw0
  have hkc : (A τ).mulVec (fun j => N τ j i) = fun j => algebraMap T.V T.Fr (k τ j i) := by
    funext j
    have h3 := congrFun (congrFun (hAN τ) j) i
    rw [Matrix.mul_apply, Matrix.map_apply] at h3
    rw [← h3]
    rfl
  rw [hkc] at hc
  rw [← isCombAt_unique hc (hu'' τ i)]
  exact hw'

end Frames

end Formalism.L2.Pj
