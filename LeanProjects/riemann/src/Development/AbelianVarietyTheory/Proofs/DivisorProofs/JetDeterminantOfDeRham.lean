import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageCorrespondence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.PeriodFamily
open GlobalTheory.LatJet GlobalTheory.LatJet.An
open scoped Classical Topology

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An.Det

theorem exists_frame (R : Type) [CommRing R] (M : Type 1) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] :
    ∃ (N : ℕ) (c : Fin N → M) (h : Fin N → Module.Dual R M), ∀ x, x = ∑ a, h a x • c a := by
  obtain ⟨N, f, g, -, -, e⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  refine ⟨N, fun a ↦ f (Pi.single a 1), fun a ↦ LinearMap.proj a ∘ₗ g, fun x ↦ ?_⟩
  have h1 : f (g x) = x := LinearMap.congr_fun e x
  conv_lhs => rw [← h1, LinearMap.pi_apply_eq_sum_univ]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  congr 2
  ext b
  simp [Pi.single_apply, eq_comm]

def DetFormula {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] (X : Obj F 𝔠 (Sp R)) (δ : X.DetOmega)
    {N : ℕ} (c : Fin N → primDR X.A) (r : (Fin (Module.finrank ℚ F) → Fin N) → R) : Prop :=
  ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (X' : Obj F 𝔠 (Sp R')) (φ : X'.A.left ⟶ X.A.left),
    X'.IsPullBy X (spMap σ) φ → ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) φ) (δ' : X'.DetOmega),
    Obj.DetCorr σ φ δ δ' → ∀ (x : Fin (Module.finrank ℚ F) → HdR X'.A) (v : Fin (Module.finrank ℚ F) → X'.Lie),
    (∀ j, IsLieImage (x j) (v j).hom) → δ' v = ∑ a, σ (r a) * ∏ j, x j (m.pull (c (a j)))

theorem exists_det_formula (H : GlobalTheory.Published.AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R]
    (X : Obj F 𝔠 (Sp R)) (δ : X.DetOmega) :
    ∃ (N : ℕ) (c : Fin N → primDR X.A) (r : (Fin (Module.finrank ℚ F) → Fin N) → R), DetFormula X δ c r := by
  obtain ⟨h1, h2, -⟩ := H.1.prim X.ab X.dim
  obtain ⟨N, c, h, hc⟩ := exists_frame R (primDR X.A)
  have L := (H.2.1 R X.A _ X.ab X.dim).1
  refine ⟨N, c, fun a ↦ δ fun j ↦ L.toLie X.rm (h (a j)), ?_⟩
  intro R' _ σ X' φ hX m δ' hδ x v hv
  letI : Algebra R R' := σ.toAlgebra
  have L' := (H.2.1 R' X'.A _ X'.ab X'.dim).1
  have hb : GrpMor.IsBC (show GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A (algebraMap R R') (spMap σ) φ from m) :=
    (H.2.2.1 R X.A _ X.ab X.dim R' X'.A φ hX.grp).1
  choose h' hh' using fun a ↦ hb.exists (h a)
  have hx : ∀ y : HdR X'.A, y = ∑ a, y (m.pull (c a)) • h' a := fun y ↦ by
    refine LinearMap.ext fun z ↦ ?_
    obtain ⟨z, rfl⟩ := hb.2 z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul s z =>
      rw [liftSemi_tmul, map_smul, map_smul, LinearMap.sum_apply]
      congr 1
      simp only [LinearMap.smul_apply, hh' _ z]
      conv_lhs => rw [hc z]
      simp only [map_sum, LinearMap.map_smulₛₗ, map_smul, smul_eq_mul]
      exact Finset.sum_congr rfl fun a _ ↦ mul_comm _ _
  have hv' : v = fun j ↦ ∑ a, x j (m.pull (c a)) • L'.toLie X'.rm (h' a) := funext fun j ↦ by
    rw [← (L'.toLie_eq_iff X'.rm).2 (hv j)]
    conv_lhs => rw [hx (x j)]
    simp only [map_sum, map_smul]
  rw [hv']
  refine (δ'.toMultilinearMap.map_sum _).trans (Finset.sum_congr rfl fun a _ ↦ ?_)
  refine (δ'.toMultilinearMap.map_smul_univ _ _).trans ?_
  rw [smul_eq_mul, mul_comm]
  congr 1
  exact hδ _ _ fun j ↦ Obj.lieCorr_of_isLieImage H σ hX m (hh' (a j)) ((L.toLie_eq_iff X.rm).1 rfl)
    ((L'.toLie_eq_iff X'.rm).1 rfl)

section Lat

variable {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))

abbrev hol : (Λ →₀ ℂ) →ₗ[ℂ] (Fin g → ℂ) := Finsupp.linearCombination ℂ fun x : Λ ↦ (x : Fin g → ℂ)

abbrev ahol : (Λ →₀ ℂ) →ₗ[ℂ] (Fin g → ℂ) := Finsupp.linearCombination ℂ fun x : Λ ↦ star (x : Fin g → ℂ)

theorem exists_comb (h : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (w : Fin g → ℂ) :
    ∃ c, hol Λ c = w ∧ ahol Λ c = 0 := by
  have key : ∀ w : Fin g → ℂ, ∃ c, hol Λ c = w ∧ ahol Λ c = star w := fun w ↦ by
    have hw : w ∈ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) := h ▸ Submodule.mem_top
    induction hw using Submodule.span_induction with
    | mem x hx => exact ⟨Finsupp.single ⟨x, hx⟩ 1, by simp, by simp⟩
    | zero => exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, h1, h2⟩ := hx
      obtain ⟨d, h3, h4⟩ := hy
      exact ⟨c + d, by rw [map_add, h1, h3], by rw [map_add, h2, h4, star_add]⟩
    | smul r x _ hx =>
      obtain ⟨c, h1, h2⟩ := hx
      refine ⟨(r : ℂ) • c, by rw [map_smul, h1]; rfl, ?_⟩
      rw [map_smul, h2]
      ext a
      simp
  obtain ⟨c, h1, h2⟩ := key w
  obtain ⟨d, h3, h4⟩ := key (Complex.I • w)
  refine ⟨(2 : ℂ)⁻¹ • (c - Complex.I • d), ?_, ?_⟩
  · rw [map_smul, map_sub, map_smul, h1, h3, smul_smul, Complex.I_mul_I]
    ext a
    simp
    ring
  · rw [map_smul, map_sub, map_smul, h2, h4, star_smul, smul_smul]
    simp

end Lat

theorem exists_lie_comb {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {S : Type} (P : S → HdR A)
    (W : S → Fin g → ℂ) (h : ∀ x, ∃ v, IsLieImage (P x) v ∧ u.IsDiff (W x) v) (c : S →₀ ℂ) :
    ∃ v, IsLieImage (Finsupp.linearCombination ℂ P c) v ∧ u.IsDiff (Finsupp.linearCombination ℂ W c) v := by
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨1, by simpa using isLieImage_one_iff.2 (zero_mem _), by simpa using UnifDifferential.isDiff_one u⟩
  | add c d hc hd =>
    obtain ⟨v, h1, h2⟩ := hc
    obtain ⟨w, h3, h4⟩ := hd
    rw [map_add, map_add]
    exact ⟨v * w, h1.add h3, UnifDifferential.isDiff_mul u ((Chart.isTan_iff _).2 h1.1) ((Chart.isTan_iff _).2 h3.1) h2 h4⟩
  | single x r =>
    obtain ⟨v, h1, h2⟩ := h x
    rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single]
    exact ⟨_, h1.smul r, UnifDifferential.isDiff_scale u h2 r⟩

theorem pair_comb {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) {M : Type 1} [AddCommGroup M] [Module ℂ M] (P : Λ → M)
    (ψ : LinearMap.BilinForm ℂ M) (h : Fin g → ℝ) (k : ℂ)
    (hψ : ∀ x x' : Λ, ψ (P x) (P x') = k * (((x : Fin g → ℂ) ⬝ᵥ
      (Matrix.diagonal fun a ↦ (h a : ℂ)).mulVec (star (x' : Fin g → ℂ))).im : ℂ)) (c d : Λ →₀ ℂ) :
    ψ (Finsupp.linearCombination ℂ P c) (Finsupp.linearCombination ℂ P d) =
      k / (2 * Complex.I) * ∑ a, h a * (hol Λ c a * ahol Λ d a - ahol Λ c a * hol Λ d a) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c c' hc hc' =>
    simp only [map_add, LinearMap.add_apply, hc, hc', Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun a _ ↦ by ring
  | single x r =>
    induction d using Finsupp.induction_linear with
    | zero => simp
    | add d d' hd hd' =>
      simp only [map_add, hd, hd', Pi.add_apply, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun a _ ↦ by ring
    | single x' r' =>
      simp only [Finsupp.linearCombination_single, map_smul, LinearMap.smul_apply, hψ, smul_eq_mul, Pi.smul_apply,
        Complex.im_eq_sub_conj, dotProduct, Matrix.mulVec_diagonal, map_sum, map_mul, Pi.star_apply, RCLike.star_def,
        Complex.conj_ofReal, Complex.conj_conj, ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun a _ ↦ by ring

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {𝔠 : FracId (FR E)} {φ : I → E →+* ℂ}

omit [Fintype I] in

theorem exists_sep [IsCMField E] (hφ : IsCMType φ) {c : Ideal (OF E)} (hc : c ≠ ⊥) (i j : I) :
    ∃ a ∈ orderC c, φ i a ≠ starRingEnd ℂ (φ j a) := by
  by_contra hh
  push_neg at hh
  obtain ⟨b, hb, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  have hb1 : algebraMap (OF E) E b ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply (OF E) (maximalRealSubfield E) E]
    simpa using hb0
  have e : φ i = ComplexEmbedding.conjugate (φ j) := by
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun x ↦ ?_
    have h1 := hh _ (algebraMap_mem_orderC c b)
    have h2 := hh (algebraMap (OF E) E b * algebraMap (𝓞 E) E x) (Subring.subset_closure (Or.inr
      ⟨_, Ideal.mul_mem_right x _ (Ideal.mem_map_of_mem _ hb), by rw [map_mul, ← IsScalarTower.algebraMap_apply]⟩))
    rw [map_mul, map_mul, map_mul, ← h1] at h2
    exact mul_left_cancel₀ ((map_ne_zero _).2 hb1) h2
  obtain rfl : i = j := (hφ (φ i)).unique (Or.inl rfl) (Or.inr e)
  exact IsTotallyComplex.complexEmbedding_not_isReal (φ i) (ComplexEmbedding.isReal_iff.2 e.symm)

theorem low_eq_zero [IsCMField E] (hφ : IsCMType φ) {c : Ideal (OF E)} (hc : c ≠ ⊥) {y : (Af E)ˣ} (T : CxPt 𝔠 φ (lattice c y))
    {ε : ℤˣ} {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P) {d : T.U.u.Λ →₀ ℂ} {j : Fin (Module.finrank ℚ (FR E))}
    (h1 : hol _ d = Pi.single j 1) (h2 : ahol _ d = 0) (i : I) : T.low i (Finsupp.linearCombination ℂ P d) = 0 := by
  obtain ⟨hs, -, -, hend, hpol⟩ := hP
  obtain ⟨χ, hχ⟩ := T.U.ah
  have hψ := pair_comb _ P T.ψ (fun a ↦ T.U.h (T.U.e a)) _ (hpol _ χ T.ψ hχ T.pol) d
  obtain ⟨a, ha, hne⟩ := exists_sep hφ hc i (T.U.e j)
  let M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    LinearMap.pi fun b ↦ φ (T.U.e b) a • LinearMap.proj b
  have hM : ∀ x ∈ T.U.u.Λ, M x ∈ T.U.u.Λ := fun x hx ↦ by
    obtain ⟨x, hx', rfl⟩ := (T.U.lat x).1 hx
    exact (T.U.lat _).2 ⟨a * x, mul_mem_lattice ha hx', by ext b; simp [M, GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]⟩
  obtain ⟨α, hα, hex⟩ := HolUnifEnd.exists_isMonHom_of_map_lattice T.X.A _ T.X.ab T.X.dim _ T.U.u M hM
  have hy := (T.cm i).1 a α hex
  obtain ⟨d', hd'⟩ : T.y i ∈ LinearMap.range (Finsupp.linearCombination ℂ P) := by
    rw [Finsupp.range_linearCombination, hs]; trivial
  have key : ∀ f : T.U.u.Λ →₀ ℂ, ∃ f', Finsupp.linearCombination ℂ P f' = push (dp0 ℂ) (𝟙 _) α (Finsupp.linearCombination ℂ P f) ∧
      ahol _ f' j = starRingEnd ℂ (φ (T.U.e j) a) * ahol _ f j := fun f ↦ by
    induction f using Finsupp.induction_linear with
    | zero => exact ⟨0, by simp, by simp⟩
    | add f g hf hg =>
      obtain ⟨f', e1, e2⟩ := hf
      obtain ⟨g', e3, e4⟩ := hg
      exact ⟨f' + g', by simp only [map_add, e1, e3], by simp only [map_add, Pi.add_apply, e2, e4, mul_add]⟩
    | single x r =>
      refine ⟨Finsupp.single ⟨M x, hM _ x.2⟩ r, ?_, ?_⟩
      · rw [Finsupp.linearCombination_single, Finsupp.linearCombination_single, map_smul, hend α M hex x ⟨M x, hM _ x.2⟩ rfl]
      · simp [M]
        ring
  obtain ⟨d'', e1, e2⟩ := key d'
  have f1 := hψ d'
  have f2 := hψ d''
  rw [e1, hd', hy, map_smul, smul_eq_mul] at f2
  rw [hd'] at f1
  simp only [h1, h2, Pi.zero_apply, zero_mul, sub_zero, Pi.single_apply, ite_mul, _root_.one_mul, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at f1 f2
  have h0 : T.ψ (Finsupp.linearCombination ℂ P d) (T.y i) = 0 := by
    refine (mul_eq_zero.1 ?_).resolve_left (sub_ne_zero.2 hne)
    rw [sub_mul, f2, f1, e2]
    ring
  simp [CxPt.low, h0]

section Jet

variable {n : ℕ} (J : JetRing ℂ I n)

def HasJet (f : (I → ℂ) → ℂ) (b : J.B) : Prop := AnalyticAt ℂ f 0 ∧ jet J f = b

variable {J}

theorem hasJet_const (a : ℂ) : HasJet J (fun _ ↦ a) (algebraMap ℂ J.B a) := ⟨analyticAt_const, Check.jet_const J a⟩

theorem HasJet.mul (hC : JetCalc) {f g : (I → ℂ) → ℂ} {a b : J.B} (h : HasJet J f a) (k : HasJet J g b) :
    HasJet J (fun z ↦ f z * g z) (a * b) :=
  ⟨h.1.mul k.1, h.2 ▸ k.2 ▸ ((hC I n J).2.1 f g h.1 k.1).1⟩

theorem HasJet.add (hC : JetCalc) {f g : (I → ℂ) → ℂ} {a b : J.B} (h : HasJet J f a) (k : HasJet J g b) :
    HasJet J (fun z ↦ f z + g z) (a + b) :=
  ⟨h.1.add k.1, h.2 ▸ k.2 ▸ ((hC I n J).2.1 f g h.1 k.1).2⟩

theorem hasJet_sum (hC : JetCalc) {S : Type} (s : Finset S) {f : S → (I → ℂ) → ℂ} {a : S → J.B} (h : ∀ x, HasJet J (f x) (a x)) :
    HasJet J (fun z ↦ ∑ x ∈ s, f x z) (∑ x ∈ s, a x) := by
  induction s using Finset.induction_on with
  | empty => simpa using hasJet_const (J := J) 0
  | insert x s hx ih => simpa only [Finset.sum_insert hx] using (h x).add hC ih

theorem hasJet_prod (hC : JetCalc) {S : Type} (s : Finset S) {f : S → (I → ℂ) → ℂ} {a : S → J.B} (h : ∀ x, HasJet J (f x) (a x)) :
    HasJet J (fun z ↦ ∏ x ∈ s, f x z) (∏ x ∈ s, a x) := by
  induction s using Finset.induction_on with
  | empty => simpa using hasJet_const (J := J) 1
  | insert x s hx ih => simpa only [Finset.prod_insert hx] using (h x).mul hC ih

theorem isBC (H : GlobalTheory.Published.AbelianDeRham) {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ))
    (m : GrpMor (dp0 ℂ) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap ℂ J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))) : m.IsBC := by
  have e : (𝟙 _ : Sp ℂ ⟶ Sp ℂ) = spMap (RingHom.id ℂ) := (Cris.spMap_id ℂ).symm
  have h := (GlobalTheory.CrysConn.isGrpPullback_refl X.A).congr e rfl
  have key : ∀ (t : Sp ℂ ⟶ Sp ℂ), t = spMap (RingHom.id ℂ) →
      ∀ m : GrpMor (dp0 ℂ) t X.A J.κ (spMap J.π) X.A (algebraMap ℂ J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A)), m.IsBC := by
    rintro _ rfl m
    exact GlobalTheory.CrysConn.isBC_of_lift H X.ab X.dim (isDPNilpotent_bot ℂ) Function.surjective_id
      ((RingHom.injective_iff_ker_eq_bot _).1 Function.injective_id) h J.nil
      (fun r ↦ ⟨_, J.π_algebraMap r⟩) rfl m (GlobalTheory.CrysConn.isGrpPullback_refl X.A)
  exact key _ e m

end Jet

section Main

variable {n : ℕ} {L : Set E} {T : CxPt 𝔠 φ L} {J : JetRing ℂ I n} {Y : Family J T.X T.δ T.low} {G : Germ Y} {ε : ℤˣ}
  {N : ℕ} {cl : Fin N → primDR G.X.A} {r : (Fin (Module.finrank ℚ (FR E)) → Fin N) → G.B}
  {d : Fin (Module.finrank ℚ (FR E)) → T.U.u.Λ →₀ ℂ}

theorem coeff_fibre (K : Coord ε G) (hδ : DetFormula G.X G.δ.1 cl r) (hd1 : ∀ j, hol _ (d j) = Pi.single j 1)
    (hd2 : ∀ j, ahol _ (d j) = 0) (z : I → ℂ) (hz : z ∈ K.V) :
    K.C z = ∑ a, G.y z (r a) * ∏ j, ∑ x ∈ (d j).support, d j x * K.P z x ((K.mor z).pull (cl (a j))) := by
  choose v hv hv' using fun j ↦ exists_lie_comb (K.U z hz).u (K.P z) _ (K.lie z hz) (d j)
  have hW : ∀ j, Finsupp.linearCombination ℂ (fun (x : T.U.u.Λ) a ↦ x.1 a + K.ζ z (T.U.e a) * starRingEnd ℂ (x.1 a)) (d j) =
      (1 : Matrix _ _ ℂ) j := fun j ↦ by
    ext a
    have e1 := congrFun (hd1 j) a
    have e2 := congrFun (hd2 j) a
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.star_apply,
      RCLike.star_def, Pi.zero_apply] at e1 e2 ⊢
    simp only [mul_add, Finset.sum_add_distrib, e1, mul_left_comm _ (K.ζ z _), ← Finset.mul_sum, e2]
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  have e1 := K.det z hz (fun j ↦ Serre.Lie.mk (K.X z).rm (v j) (hv j).1) 1 fun j ↦ by
    rw [← hW j]; exact hv' j
  have e2 := hδ ℂ (G.y z : G.B →+* ℂ) (K.X z) (K.q z) (K.pull z) (K.mor z) (K.δ z).1 (K.corr z)
    (fun j ↦ Finsupp.linearCombination ℂ (K.P z) (d j)) (fun j ↦ Serre.Lie.mk (K.X z).rm (v j) (hv j).1) hv
  replace e1 := e1.trans ((congrArg (K.C z * ·) Matrix.det_one).trans (_root_.mul_one _))
  refine (e1.symm.trans e2).trans (Finset.sum_congr rfl fun a _ ↦ congrArg _ (Finset.prod_congr rfl fun j _ ↦ ?_))
  rw [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  rfl

theorem coeff_origin (H : GlobalTheory.Published.AbelianDeRham) {P : T.U.u.Λ →+ HdR T.X.A} (hP : IsPeriodMap ε T.U.u P)
    (hδ : DetFormula G.X G.δ.1 cl r) (hd1 : ∀ j, hol _ (d j) = Pi.single j 1)
    (hlow : ∀ j i, T.low i (Finsupp.linearCombination ℂ P (d j)) = 0)
    (m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q)
    {D : T.U.u.Λ → Crys J.κ (spMap J.π) T.X.A} (hD : ∀ x, Y.mor.Corr (P x) (D x)) :
    G.e * ∑ a, G.j (r a) * ∏ j, ∑ x ∈ (d j).support, algebraMap ℂ J.B (d j x) *
      crysToDR J.κ Y.pull.grp (D x) (m'.pull (cl (a j))) = algebraMap ℂ J.B T.C := by
  obtain ⟨D', hD'⟩ : ∃ D' : Fin (Module.finrank ℚ (FR E)) → Crys J.κ (spMap J.π) T.X.A,
      ∀ j cc, D' j cc = ∑ x ∈ (d j).support, algebraMap ℂ J.B (d j x) * D x cc :=
    ⟨fun j ↦ ∑ x ∈ (d j).support, algebraMap ℂ J.B (d j x) • D x, fun j cc ↦ LinearMap.sum_apply _ _ _⟩
  have L' := (H.2.1 _ Y.X'.A _ Y.X'.ab Y.X'.dim).1
  choose v hv hv' using fun j ↦ exists_lie_comb T.U.u P _ hP.2.2.1 (d j)
  have e1 := T.det (fun j ↦ Serre.Lie.mk T.X.rm (v j) (hv j).1) 1 fun j ↦ by
    have : (1 : Matrix _ _ ℂ) j = hol _ (d j) := by
      rw [hd1]
      ext a
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this]; exact hv' j
  replace e1 := e1.trans ((congrArg (T.C * ·) Matrix.det_one).trans (_root_.mul_one _))
  have hL : ∀ j, IsLieImage (crysToDR J.κ Y.pull.grp (D' j)) (L'.toLie Y.X'.rm (crysToDR J.κ Y.pull.grp (D' j))).hom :=
    fun j ↦ (L'.toLie_eq_iff Y.X'.rm).1 rfl
  have hJ : ∀ j, IsJetElt J T.X T.low Y.mor (Finsupp.linearCombination ℂ P (d j)) (D' j) := fun j cc ↦ by
    rw [hD', Finset.sum_eq_zero (s := Finset.univ) fun i _ ↦ by rw [hlow, LinearMap.zero_apply, map_zero, mul_zero], add_zero,
      Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [hD x cc, ← map_mul]
    rfl
  have e2 := Y.gen (fun j ↦ Finsupp.linearCombination ℂ P (d j)) D' (fun j ↦ Serre.Lie.mk T.X.rm (v j) (hv j).1)
    (fun j ↦ L'.toLie Y.X'.rm (crysToDR J.κ Y.pull.grp (D' j))) fun j ↦ ⟨hJ j, hv j, hL j⟩
  have e3 := hδ J.B (G.j : G.B →+* J.B) Y.X' G.q G.pull m' G.δ''.1 G.corr _ _ hL
  refine Eq.trans ?_ (e2.trans (congrArg _ e1))
  refine Eq.trans ?_ (DFunLike.congr_fun G.he _).symm
  refine congrArg (G.e * ·) (Eq.trans ?_ e3.symm)
  exact Finset.sum_congr rfl fun a _ ↦ congrArg _ (Finset.prod_congr rfl fun j _ ↦ (hD' j _).symm)

end Main

theorem jetDet : GlobalTheory.Published.AbelianDeRham → JetCalc → JetDet := by
  intro H hC ε E _ _ _ I _ 𝔠 φ c y hφ hc n T J Y G K
  obtain ⟨N, cl, r, hδ⟩ := exists_det_formula H G.X G.δ.1
  choose d hd1 hd2 using fun j : Fin (Module.finrank ℚ (FR E)) ↦ exists_comb _ T.U.u.full (Pi.single j 1)
  have hV := K.isOpen.mem_nhds K.zero
  have m' : GrpMor (dp0 G.B) (𝟙 _) G.X.A (dp0 J.B) (𝟙 _) Y.X'.A (G.j : G.B →+* J.B) (spMap (G.j : G.B →+* J.B)) G.q :=
    GrpMor.of_isGrpPullback (isDPMorphism_of_eq_bot _ rfl _ _) ((Category.comp_id _).trans (Category.id_comp _).symm) G.pull.grp
  choose D hD using fun x : T.U.u.Λ ↦ (isBC H T.X Y.mor).exists (K.P₀ x)
  have hJ : HasJet J (fun z ↦ ∑ a, G.y z (r a) * ∏ j, ∑ x ∈ (d j).support, d j x * K.P z x ((K.mor z).pull (cl (a j))))
      (∑ a, G.j (r a) * ∏ j, ∑ x ∈ (d j).support, algebraMap ℂ J.B (d j x) *
        crysToDR J.κ Y.pull.grp (D x) (m'.pull (cl (a j)))) :=
    hasJet_sum hC Finset.univ fun a ↦
      HasJet.mul hC ⟨SCV.analyticAt_of_differentiableOn (G.hol (r a)) (G.isOpen.mem_nhds G.zero), (G.jet_eq (r a)).symm⟩
        (hasJet_prod hC Finset.univ fun j ↦ hasJet_sum hC (d j).support fun x ↦ (hasJet_const (d j x)).mul hC
          ⟨SCV.analyticAt_of_differentiableOn (K.P_hol x (cl (a j))) hV, (K.horiz m' x (D x) (hD x) (cl (a j))).symm⟩)
  have hev := Filter.eventually_of_mem hV (coeff_fibre K hδ hd1 hd2)
  refine ⟨hJ.1.congr (Filter.EventuallyEq.symm hev), ?_⟩
  exact (congrArg (G.e * ·) ((Check.jet_congr J hev).trans hJ.2)).trans
    (coeff_origin H K.per hδ hd1 (fun j ↦ low_eq_zero hφ hc T K.per (hd1 j) (hd2 j)) m' hD)

end GlobalTheory.LatJet.An.Det
