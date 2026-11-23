import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupStalkNoetherianNormalFractionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPullComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeEquivOfSameCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagEndIsMonHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CongModOfMkEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLabOntoAndKer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfNatCastEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOOfPowEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.ClassCore

def IsSum {K X : Type} [NormedAddCommGroup K] [AddCommGroup X] (m : ℕ) (t : (Fin 8 → X) → K) (ν : Fin 8 → X) (v : K) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → X), ∀ S : Finset (Fin 8 → X), (∀ μ ∈ S, ∀ u, CongMod m (μ u) (ν u)) →
    (∀ μ ∈ S₀, (∀ u, CongMod m (μ u) (ν u)) → μ ∈ S) → ‖v - ∑ μ ∈ S, t μ‖ ≤ δ

theorem cong_symm {X : Type} [AddCommGroup X] {m : ℕ} {x y : X} (h : CongMod m x y) : CongMod m y x := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨-w, by simp⟩

theorem cong_trans {X : Type} [AddCommGroup X] {m : ℕ} {x y z : X} (h : CongMod m x y) (h' : CongMod m y z) :
    CongMod m x z := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨w', rfl⟩ := h'
  exact ⟨w' + w, by rw [smul_add, add_assoc]⟩

theorem cong_map {X Y : Type} [AddCommGroup X] [AddCommGroup Y] {m : ℕ} (e : X →+ Y) {x y : X} (h : CongMod m x y) :
    CongMod m (e x) (e y) := by
  obtain ⟨w, rfl⟩ := h
  exact ⟨e w, by simp⟩

theorem IsSum.unique {K X : Type} [NormedAddCommGroup K] [AddCommGroup X] {m : ℕ} {t : (Fin 8 → X) → K} {ν ν' : Fin 8 → X}
    {v v' : K} (h : IsSum m t ν v) (h' : IsSum m t ν' v') (hc : ∀ u, CongMod m (ν u) (ν' u)) : v = v' := by
  classical
  refine eq_of_norm_sub_le_zero (le_of_forall_pos_le_add fun δ hδ => ?_)
  obtain ⟨S₀, hS⟩ := h (δ / 2) (by positivity)
  obtain ⟨S₀', hS'⟩ := h' (δ / 2) (by positivity)
  let S := (S₀ ∪ S₀').filter fun μ => ∀ u, CongMod m (μ u) (ν u)
  have h1 := hS S (fun μ hμ => (Finset.mem_filter.1 hμ).2)
    (fun μ hμ hh => Finset.mem_filter.2 ⟨Finset.mem_union_left _ hμ, hh⟩)
  have h2 := hS' S (fun μ hμ u => cong_trans ((Finset.mem_filter.1 hμ).2 u) (hc u))
    (fun μ hμ hh => Finset.mem_filter.2 ⟨Finset.mem_union_right _ hμ, fun u => cong_trans (hh u) (cong_symm (hc u))⟩)
  have h3 : v - v' = (v - ∑ μ ∈ S, t μ) - (v' - ∑ μ ∈ S, t μ) := by abel
  rw [h3]
  linarith [norm_sub_le (v - ∑ μ ∈ S, t μ) (v' - ∑ μ ∈ S, t μ)]

theorem IsSum.comp {K X Y : Type} [NormedAddCommGroup K] [AddCommGroup X] [AddCommGroup Y] {m : ℕ} {t : (Fin 8 → Y) → K}
    (e : X ≃+ Y) {ν : Fin 8 → X} {v : K} (h : IsSum m t (fun u => e (ν u)) v) :
    IsSum m (fun μ => t fun u => e (μ u)) ν v := by
  classical
  intro δ hδ
  obtain ⟨S₀, hS⟩ := h δ hδ
  let E : (Fin 8 → X) ≃ (Fin 8 → Y) := Equiv.piCongrRight fun _ => e.toEquiv
  refine ⟨S₀.map E.symm.toEmbedding, fun S h1 h2 => ?_⟩
  have := hS (S.map E.toEmbedding) (fun μ hμ u => by
    obtain ⟨μ', hμ', rfl⟩ := Finset.mem_map.1 hμ
    exact cong_map e.toAddMonoidHom (h1 μ' hμ' u)) (fun μ hμ hh => by
    refine Finset.mem_map.2 ⟨E.symm μ, h2 _ (Finset.mem_map_of_mem _ hμ) fun u => ?_, E.apply_symm_apply μ⟩
    simpa [E] using cong_map e.symm.toAddMonoidHom (hh u))
  rwa [Finset.sum_map] at this

theorem det_eq_one {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (γ : X ≃ₗ[ℤ] X) {L : ℕ} (hL : 3 ≤ L)
    (h : ∀ x, CongMod L (γ x) x) : LinearMap.det γ.toLinearMap = 1 := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  have h1 : ((LinearMap.det γ.toLinearMap : ℤ) : ZMod L) = 1 := by
    rw [← LinearMap.det_toMatrix b, ← eq_intCast (Int.castRingHom (ZMod L)), RingHom.map_det]
    have : (Int.castRingHom (ZMod L)).mapMatrix (LinearMap.toMatrix b b γ.toLinearMap) = 1 := by
      ext i j
      obtain ⟨w, hw⟩ := h (b j)
      simp [LinearMap.toMatrix_apply, hw, Matrix.one_apply, Finsupp.single_apply, eq_comm]
    rw [this, Matrix.det_one]
  rcases Int.isUnit_iff.1 γ.isUnit_det' with h2 | h2
  · exact h2
  · rw [h2] at h1
    have h3 : ((2 : ℕ) : ZMod L) = 0 := by
      have : ((-1 : ℤ) : ZMod L) = -1 := by simp
      rw [this] at h1
      push_cast
      linear_combination -h1
    have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff _ _).1 h3)
    omega

theorem cong_of_mk_eq {X : Type} [AddCommGroup X] (hX : ∀ (d : ℕ) (x : X), d ≠ 0 → d • x = 0 → x = 0) {d L M : ℕ}
    (hd : d ≠ 0) (hM : M = d * L) {μ ν : Fin 8 → X}
    (h : d • (QuotientAddGroup.mk μ : ModN M (Fin 8 → X)) = d • QuotientAddGroup.mk ν) (u : Fin 8) :
    CongMod L (μ u) (ν u) := by
  rw [← QuotientAddGroup.mk_nsmul, ← QuotientAddGroup.mk_nsmul, eq_comm, QuotientAddGroup.eq] at h
  obtain ⟨w, hw⟩ := h
  have h1 : M • w u = -(d • ν u) + d • μ u := congrFun hw u
  refine ⟨w u, sub_eq_zero.1 (hX d _ hd ?_)⟩
  rw [smul_sub, smul_add, smul_smul, ← hM, h1]
  abel

section Geometry

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem normal_pred {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
    (X : Setup F W i) : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X.M.Z := by
  first
  | exact X.normal
  | exact (GlobalTheory.isNormalScheme_iff_pred _).1 X.normal

theorem three_le_level (X₁ : Setup F W i) : 3 ≤ X₁.S.r * X₁.S.N := by
  have h1 := X₁.S.r_pos
  have h2 : 2 ≤ X₁.ρ.n ^ X₁.ρ.k :=
    X₁.ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := X₁.ρ.two_le; omega) _)
  have h3 := X₁.ρ.N_eq
  nlinarith

theorem exists_iso (D : Deep X₁ ε₁) {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (c c' : CTrait X₁ p z₁)
    {y y' : Sp (OO p) ⟶ D.X.M.Z} (h : y ≫ D.q = c.y) (h' : y' ≫ D.q = c'.y) (hc : y' (cPt p) = y (cPt p))
    {yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)}
    {yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c'.T.D.toPre.X)}
    (hl : IsLab D.X D.ε (D.lift c y h) yy) (hl' : IsLab D.X D.ε (D.lift c' y' h') yy') :
    ∃ κ : c.T.D.toPre.X ≃ₗ[ℤ] c'.T.D.toPre.X,
      ∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (fun u => κ (μ u)) :=
  GlobalTheory.Poinc.lattice_equiv_of_same_centre g n F W Z i D.X X₁.one_le X₁.three_le X₁.odd X₁.imm X₁.e8 X₁.thetaInt D.proj D.ε D.diag p (y (cPt p))
    (D.lift c y h) ⟨y', hc, c'.T, c'.ι, c'.int, (D.lift c' y' h').comm⟩ yy yy' hl hl'

theorem eq_zero_of_lifts (hε : IsDiagEnd F W X₁.ρ.P X₁.u ε₁) (D : Deep X₁ ε₁) {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z}
    {z₂ : D.X.M.Z} (hz : D.q z₂ = z₁) (y₀ : Sp (OO p) ⟶ D.X.M.Z) (h₀ : y₀ (cPt p) = z₂) {b : D.X.Ω₁}
    (hb : b ∈ D.X.M.O z₂)
    (hv : ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ →
      ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ →
      ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy →
        D.Compat yy₁ yy → D.X.M.val (gPt p ≫ y) b = 0) : b = 0 := by
  haveI := X₁.imm
  subst h₀
  refine GlobalTheory.Poinc.eq_zero_of_val_cen_eq_zero D.X.o₁ D.X.Ω₁ D.X.M (normal_pred D.X) (D.X.π ⁻¹ᵁ i.opensRange) ?_ p y₀ b hb fun y hy => ?_
  · refine ⟨D.X.M.pt (closedPoint D.X.Ω₁), ?_⟩
    show (D.X.M.pt ≫ D.X.π) (closedPoint D.X.Ω₁) ∈ Set.range i
    rw [D.X.comp]
    exact ⟨(spMap D.X.S.R.val.toRingHom ≫ D.X.u) (closedPoint D.X.Ω₁), rfl⟩
  · obtain ⟨c, hc⟩ := GlobalTheory.Poinc.GCTrait.exists_cTrait g n F W Z i X₁ X₁.one_le X₁.three_le X₁.odd X₁.imm p (y ≫ D.q) (by
      rw [Category.assoc, D.comp]
      rintro _ ⟨w, rfl⟩
      exact hy.2 ⟨w, rfl⟩)
    let c' : CTrait X₁ p z₁ := ⟨c.y, by rw [hc, ← hz, ← hy.1]; rfl, c.T, c.ι, c.int, c.comm⟩
    obtain ⟨yy₁, h₁⟩ := GlobalTheory.Poinc.exists_isLab g n F W Z i X₁ X₁.one_le X₁.three_le X₁.odd X₁.imm X₁.e8 X₁.thetaInt X₁.projM ε₁ hε
      p z₁ c'
    obtain ⟨yy, h₂, h₃⟩ := GlobalTheory.Poinc.GLift.labels_lift g n F W Z i X₁ X₁.one_le X₁.three_le X₁.odd X₁.imm X₁.e8 X₁.thetaInt X₁.projM ε₁ hε
      D p z₁ c' yy₁ h₁ y hc.symm
    exact hv c' yy₁ h₁ y hc.symm hy.1 yy h₂ h₃

theorem inv_mem_iff {o Ω B : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CommRing B] (M : RatModel o Ω) (φ : B →+* Ω)
    {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (hB : ∀ b, φ b ∈ M.O (y (cPt p))) {𝔷 : Ideal B} (h𝔷 : 𝔷.IsMaximal)
    (hlt : ∀ b ∈ 𝔷, ‖M.val (gPt p ≫ y) (φ b)‖ < 1) (b : B) : b ∈ 𝔷 ↔ (φ b = 0 ∨ (φ b)⁻¹ ∉ M.O (y (cPt p))) := by
  let ψ : B →+* M.O (y (cPt p)) := φ.codRestrict _ hB
  have h1 : 𝔷 = (maximalIdeal (M.O (y (cPt p)))).comap ψ :=
    h𝔷.eq_of_le (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top) fun b hb =>
      (RatModel.norm_val_lt_one_iff rfl (hB b)).1 (hlt b hb)
  rw [h1, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, RatModel.isUnit_O_iff, not_and_or, not_not]
  rfl

end Geometry

theorem classSums_integralClosure : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (id : ℤ → ℤ) g p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ c : CTrait X₁ p z₁, (∀ a, Φ.ev y a = c.val a) ∧ ∃ e : Φ.X y ≃ₗ[ℤ] c.T.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = c.sc * c.T.β (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ →ₗ[ℤ] Φ.X y) (Q : Type) (t : ∀ y, (Fin 8 → Φ.X y) → Q → PadicAlgCl p) (f : (Fin 8 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearMap.id ∧ (∀ y, IsUnimodMod ℤ N (k y)) ∧ Φ.IsTerms W t ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → f c κ = f c' κ) ∧ (∀ y c κ (ε : ℝ), 0 < ε → ∃ S₀ : Finset (Fin 8 → Φ.X y), ∀ S : Finset (Fin 8 → Φ.X y), (∀ μ ∈ S, ∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ ∈ S₀, (∀ u, CongMod N (μ u) (k y (c u))) → μ ∈ S) → ‖ev' y (f c κ) - ∑ μ ∈ S, t y μ κ‖ ≤ ε) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ →ₗ[ℤ] Φ.X y₀, (N : ℤ) ∣ LinearMap.det γ - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (f c κ) = f (fun u => γ (c u)) κ := by
  intro g n F W Z i X₁ p _ z₁ Φ hΦ y₀ N₀
  have hg := X₁.one_le
  have hn := X₁.three_le
  have ho := X₁.odd
  have hi := X₁.imm
  have hE := X₁.e8
  have hT := X₁.thetaInt
  have hP := X₁.projM
  classical
  obtain ⟨ε₁, hε, -⟩ := GlobalTheory.Poinc.exists_diagEnd_isMonHom g n F W _ X₁.ρ.P X₁.u X₁.sharp
  obtain ⟨D, hD⟩ := GlobalTheory.Poinc.GDeep.exists_deep g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε N₀
  refine ⟨D.m, hD, D.dvd, D.X.Ω₁, inferInstance, D.alg, D.fd, D.gal, ?_⟩
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  intro 𝔷 h𝔷 ev' hev _ hlt
  obtain ⟨hB, hmax, hsep, hpt⟩ := GlobalTheory.Poinc.integralClosure_stalk_fibre X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q (normal_pred D.X) D.fin D.gen z₁
  obtain ⟨z₂, hz₂, hz𝔷⟩ := hmax 𝔷 h𝔷

  have hcen : ∀ y : Sp (OO p) ⟶ D.X.M.Z, D.q (y (cPt p)) = z₁ →
      (∀ b ∈ 𝔷, ‖D.X.M.val (gPt p ≫ y) (b : D.X.Ω₁)‖ < 1) → y (cPt p) = z₂ := by
    intro y hy hb
    refine hsep _ _ hy hz₂ fun b => ?_
    have h1 := (inv_mem_iff D.X.M (integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁).val.toRingHom y
      (fun b => (hB b).1 b.2 _ hy) h𝔷 hb b).symm.trans (hz𝔷 b)
    by_cases h0 : (b : D.X.Ω₁) = 0
    · simp [h0]
    · have h2 : ((b : D.X.Ω₁) = 0 ∨ (b : D.X.Ω₁)⁻¹ ∉ D.X.M.O (y (cPt p))) ↔ _ := h1
      simpa [h0, not_iff_not] using h2
  have hcen' : ∀ y : Sp (OO p) ⟶ D.X.M.Z, y (cPt p) = z₂ → ∀ b ∈ 𝔷, ‖D.X.M.val (gPt p ≫ y) (b : D.X.Ω₁)‖ < 1 := by
    intro y hy b hb
    rw [RatModel.norm_val_lt_one_iff hy ((hB b).1 b.2 _ hz₂), RatModel.isUnit_O_iff, not_and_or, not_not]
    exact (hz𝔷 b).1 hb
  obtain ⟨f, t, hf, ht⟩ := GlobalTheory.Poinc.GSum.main g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D p z₁ z₂ hz₂
  have hsum : ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ →
      ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ →
      ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy →
        D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν →
          IsSum D.m (fun μ => t c yy₁ μ κ) ν (D.X.M.val (gPt p ≫ y) (f a κ)) :=
    fun c yy₁ h₁ => (ht c yy₁ h₁).2.2
  choose c hcv e he using hΦ
  choose yy₁ hl₁ using fun y => GlobalTheory.Poinc.exists_isLab g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε p z₁ (c y)
  choose Y hYq hYv using fun y => hpt p (c y).y (c y).cen (ev' y) fun a => (hev y a).trans (hcv y a)
  have hYc : ∀ y, Y y (cPt p) = z₂ := fun y => hcen _ (by rw [← (c y).cen, ← hYq y]; rfl) fun b hb => by
    rw [← hYv]; exact hlt y b hb
  choose yy hl hcp using fun y =>
    GlobalTheory.Poinc.GLift.labels_lift g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D p z₁ (c y) (yy₁ y) (hl₁ y) (Y y) (hYq y)
  have hsurj := (GlobalTheory.Poinc.isLab_onto_and_ker g n F W Z i D.X hg hn ho hi hE hT D.proj D.ε D.diag p _ _ _ (hl y₀)).1
  choose lb hlb using fun ν : Fin 8 → (c y₀).T.D.toPre.X => hsurj (QuotientAddGroup.mk ν)

  have hsub : ∀ {b b' : D.X.Ω₁}, b ∈ D.X.M.O z₂ → b' ∈ D.X.M.O z₂ →
      (∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ →
      ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ →
      ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy →
        D.Compat yy₁ yy → D.X.M.val (gPt p ≫ y) b = D.X.M.val (gPt p ≫ y) b') → b = b' := by
    intro b b' hb hb' hv
    refine sub_eq_zero.1 (eq_zero_of_lifts hε D hz₂ (Y y₀) (hYc y₀) (sub_mem hb hb') fun c y₁ h₁ y h hc y₂ h₂ h₃ => ?_)
    exact (map_sub (RatModel.valHomOf (gPt p ≫ y) z₂ (RatModel.gPt_specializes hc)) ⟨b, hb⟩ ⟨b', hb'⟩).trans
      (sub_eq_zero.2 (hv c y₁ h₁ y h hc y₂ h₂ h₃))

  have hwd : ∀ a a' ν ν' κ, yy y₀ a = QuotientAddGroup.mk ν → yy y₀ a' = QuotientAddGroup.mk ν' →
      (∀ u, CongMod D.m (ν u) (ν' u)) → f a κ = f a' κ := by
    intro a a' ν ν' κ ha ha' hν
    refine hsub (hf _ _ _ hz₂) (hf _ _ _ hz₂) fun c' y₁ h₁ y h hc y₂ h₂ h₃ => ?_
    obtain ⟨k, hk⟩ := exists_iso D (c y₀) c' (hYq y₀) h (hc.trans (hYc y₀).symm) (hl y₀) h₂
    exact (hsum c' y₁ h₁ y h hc y₂ h₂ h₃ a _ κ (hk _ _ ha)).unique (hsum c' y₁ h₁ y h hc y₂ h₂ h₃ a' _ κ (hk _ _ ha'))
      fun u => cong_map k.toLinearMap.toAddMonoidHom (hν u)

  have hk : ∃ k : ∀ y, Φ.X y₀ ≃ₗ[ℤ] Φ.X y, k y₀ = LinearEquiv.refl ℤ _ ∧ ∀ y a (ν : Fin 8 → Φ.X y₀),
      yy y₀ a = QuotientAddGroup.mk (fun u => e y₀ (ν u)) → yy y a = QuotientAddGroup.mk fun u => e y (k y (ν u)) := by
    choose k hk using fun y => exists_iso D (c y₀) (c y) (hYq y₀) (hYq y) ((hYc y).trans (hYc y₀).symm) (hl y₀) (hl y)
    refine ⟨Function.update (fun y => (e y₀).trans ((k y).trans (e y).symm)) y₀ (LinearEquiv.refl ℤ _),
      Function.update_self _ _ _, fun y a ν ha => ?_⟩
    by_cases hy : y = y₀
    · subst hy
      rw [Function.update_self]
      exact ha
    · rw [Function.update_of_ne hy]
      simpa using hk y a _ ha
  obtain ⟨k, hk₀, hk⟩ := hk
  have hq : ∀ y (μ : Fin 8 → Φ.X y), Φ.sc y * qW W (Φ.β y) μ = (c y).sc * (qW W (c y).T.β (fun u => e y (μ u)) : ℤ) := by
    intro y μ
    simp only [qW, Int.cast_sum, Int.cast_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [mul_left_comm, he, mul_left_comm]
  refine ⟨fun y => (k y).toLinearMap, X₁.S.HH X₁.M z₁, fun y μ κ => t (c y) (yy₁ y) (fun u => e y (μ u)) κ,
    fun ν κ => ⟨f (lb fun u => e y₀ (ν u)) κ, (hB _).2 (hf _ _)⟩, by beta_reduce; rw [hk₀]; rfl,
    fun y => ⟨fun a x => ⟨0, by simp⟩, (k y).symm, by simp⟩, ⟨fun y μ κ => ?_, fun y μ => ?_⟩, fun ν ν' κ hν => ?_,
    fun y ν κ => ?_, fun σ hσ => ?_⟩
  · rw [hq]
    exact (ht _ _ (hl₁ y)).1 _ _
  · rw [hq]
    exact (ht _ _ (hl₁ y)).2.1 _
  · exact Subtype.ext (hwd _ _ _ _ κ (hlb _) (hlb _) fun u => cong_map (e y₀).toLinearMap.toAddMonoidHom (hν u))
  · rw [hYv]
    exact (hsum _ _ (hl₁ y) _ (hYq y) (hYc y) _ (hl y) (hcp y) _ _ κ (hk y _ ν (hlb _))).comp (e y).toAddEquiv
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ := (X₁.M.stalkHom z₁).toAlgebra
  haveI : IsScalarTower (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ D.X.Ω₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨hdom, hfr, -, -⟩ := GlobalTheory.Poinc.stalk_isNoetherian_normal_fractionRing g n F W Z i X₁ z₁
  haveI := D.fd
  obtain ⟨τ, hτ⟩ : ∃ τ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁, ∀ b : integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁,
      τ (b : D.X.Ω₁) = (σ b : D.X.Ω₁) := by
    refine ⟨(galRestrict (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ D.X.Ω₁ _).symm σ, fun b => ?_⟩
    have := algebraMap_galRestrict_apply (X₁.M.Z.presheaf.stalk z₁)
      ((galRestrict (X₁.M.Z.presheaf.stalk z₁) X₁.Ω₁ D.X.Ω₁ _).symm σ) b
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  obtain ⟨s, hs, hsq, hsv⟩ := GlobalTheory.Poinc.GalAut.autAct X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q (normal_pred D.X) D.fin D.gen τ
  obtain ⟨a, ha, hga⟩ := GlobalTheory.Poinc.GalLab.main g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D τ s hs

  have hconj : ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ →
      ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ →
      ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy →
        D.Compat yy₁ yy → ∃ (h' : (y ≫ s) ≫ D.q = c.y)
          (yy' : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), (y ≫ s) (cPt p) = z₂ ∧
          IsLab D.X D.ε (D.lift c (y ≫ s) h') yy' ∧ D.Compat yy₁ yy' ∧ ∀ x, yy' x = yy (a x) := by
    intro c' y₁ h₁ y h hc y₂ h₂ h₃
    have h' : (y ≫ s) ≫ D.q = c'.y := by rw [Category.assoc, hsq, h]
    obtain ⟨yy', h₄, h₅⟩ := GlobalTheory.Poinc.GLift.labels_lift g n F W Z i X₁ hg hn ho hi hE hT hP ε₁ hε D p z₁ c' y₁ h₁ (y ≫ s) h'
    refine ⟨h', yy', hcen _ (by rw [← c'.cen, ← h']; rfl) fun b hb => ?_, h₄, h₅,
      hga p z₁ c' y₁ h₁ y h h' y₂ yy' h₂ h₃ h₄ h₅⟩
    rw [← Category.assoc, hsv, hτ]
    exact hcen' y hc _ (by rw [← hσ] at hb; exact hb)
  have hτf : ∀ x κ, τ (f x κ) = f (a x) κ := by
    intro x κ
    have hm : τ (f x κ) ∈ D.X.M.O z₂ := by
      rw [hτ ⟨f x κ, (hB _).2 (hf _ _)⟩]
      exact (hB _).1 (Subtype.prop _) _ hz₂
    refine hsub hm (hf _ _ _ hz₂) fun c' y₁ h₁ y h hc y₂ h₂ h₃ => ?_
    obtain ⟨h', yy', hc', h₄, h₅, h₆⟩ := hconj c' y₁ h₁ y h hc y₂ h₂ h₃
    obtain ⟨ν, hν⟩ := QuotientAddGroup.mk_surjective (y₂ (a x))
    rw [← hsv, Category.assoc]
    exact (hsum c' y₁ h₁ _ h' hc' yy' h₄ h₅ x ν κ ((h₆ x).trans hν.symm)).unique
      (hsum c' y₁ h₁ y h hc y₂ h₂ h₃ (a x) ν κ hν.symm) fun u => ⟨0, by simp⟩
  obtain ⟨h', yy', hc', h₄, -, h₆⟩ := hconj _ _ (hl₁ y₀) _ (hYq y₀) (hYc y₀) _ (hl y₀) (hcp y₀)
  obtain ⟨κσ, hκσ⟩ := exists_iso D (c y₀) (c y₀) (hYq y₀) h' (hc'.trans (hYc y₀).symm) (hl y₀) h₄
  let γ : Φ.X y₀ ≃ₗ[ℤ] Φ.X y₀ := (e y₀).trans (κσ.trans (e y₀).symm)
  have hγ : ∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x := by
    intro x
    have hL := three_le_level X₁
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]
      exact (D.dvd.trans (dvd_pow_self _ two_ne_zero)).mul_left _
    have hM := (Nat.div_mul_cancel hdvd).symm
    have hd : D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N) ≠ 0 := fun h0 => by
      have := three_le_level D.X
      rw [h0] at hM
      omega
    obtain ⟨a₁, ha₁⟩ := D.lab_range (lb fun _ => e y₀ x)
    have h1 := ha a₁
    rw [ha₁, map_nsmul] at h1
    have h2 := congrArg (yy y₀) h1
    rw [map_nsmul, map_nsmul, ← h₆, hκσ _ _ (hlb _), hlb] at h2
    have h3 := cong_of_mk_eq (fun d x hd hx => by
      have h4 : (d : ℤ) • (e y₀).symm x = 0 := by rw [natCast_zsmul, ← map_nsmul, hx, map_zero]
      have h5 : (e y₀).symm x = 0 := (smul_eq_zero.1 h4).resolve_left (by exact_mod_cast hd)
      simpa using congrArg (e y₀) h5) hd hM h2 0
    simpa [γ] using cong_map (e y₀).symm.toLinearMap.toAddMonoidHom h3
  refine ⟨γ.toLinearMap, by rw [det_eq_one γ (three_le_level X₁) hγ]; simp, hγ, fun ν κ => Subtype.ext ?_⟩
  rw [← hτ]
  refine (hτf _ κ).trans (hwd _ _ _ _ κ ((h₆ _).symm.trans (hκσ _ _ (hlb _))) (hlb _) fun u => ⟨0, by simp [γ]⟩)

end GlobalTheory.Poinc.ClassCore
