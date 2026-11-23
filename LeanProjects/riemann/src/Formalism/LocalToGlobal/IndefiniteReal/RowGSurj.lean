import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.InBlock
import Formalism.LocalToGlobal.IndefiniteReal.CxPassSand

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.L2.GlobalTheoryTheory.DivPassage

namespace In3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  (I : In3 K G Pl0 I0 Ty T m)

theorem mem_RRg {x : Fin I.Sg.D → K} : x ∈ I.Sg.RR ↔ ∀ w : HeightOneSpectrum (𝓞 K), ∃ c ∈ w.asIdeal.primeCompl,
    ∃ z ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ (I.X.μ w),
      I.X.rowMat I.cg false (I.X.μ w) *ᵥ z = c • x := by
  simp only [Formalism.L2.Indef.IndefData.RR, Formalism.DivisionValues.glueLat, Submodule.mem_iInf, Formalism.HermitianLatticesTheory.localization₂, Formalism.HermitianLatticesTheory.locS,
    Formalism.DivisionValues.matLat, Submodule.mem_map]
  rfl

theorem mem_RRb (b : Bool) {x : Fin (I.Sb b).D → K} : x ∈ (I.Sb b).RR ↔ ∀ w : HeightOneSpectrum (𝓞 K),
    ∃ c ∈ w.asIdeal.primeCompl, ∃ z ∈ (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).abelian₂ (I.X.μ w),
      I.X.rowMat I.cr b (I.X.μ w) *ᵥ z = c • x := by
  simp only [Formalism.L2.Indef.IndefData.RR, Formalism.DivisionValues.glueLat, Submodule.mem_iInf, Formalism.HermitianLatticesTheory.localization₂, Formalism.HermitianLatticesTheory.locS,
    Formalism.DivisionValues.matLat, Submodule.mem_map]
  rfl

section Prin

variable {I} {s : ℕ} (hH : I.Hyp s)
include hH

theorem hZ_of (t : T) : ∀ g : G, I.X.Z t ≤ (I.X.Z t).comap ((I.A.fam.R t).r g) :=
  fun g _ hz => hH.stable.1 t (Sum.inr g) (Submodule.mem_map_of_mem hz)

theorem key_g (t : T) (x : Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t) → K) :
    I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.X.rowMat I.cg false t *ᵥ x)) =
      I.X.Θ t (I.X.jR t (I.cg.toR I.X.zs false t x)) := by
  have h1 : I.iCg (cpt I.A3.fam3.base3.v0.embedding (I.X.rowMat I.cg false t *ᵥ x)) =
      I.X.iC I.cg false t (cpt I.A3.fam3.base3.v0.embedding x) := by
    rw [cpt_mulVec, CxData.rowMat, kMat_map _ (hH.ratMug t)]
    refine relMat_spec _ _ (fun k => ?_) _
    have e : LinearMap.range (I.X.iC I.cg false t) = LinearMap.range I.iCg := (hH.h2g.2 t).2
    rw [← e]
    exact ⟨_, rfl⟩
  rw [h1, CxData.iC_eq_comp, CxData.lin_uQ_cpt]

theorem inj_g {x y : Fin I.Sg.D → K}
    (h : I.iCg (cpt I.A3.fam3.base3.v0.embedding x) = I.iCg (cpt I.A3.fam3.base3.v0.embedding y)) : x = y := by
  have h1 : cpt I.A3.fam3.base3.v0.embedding x = cpt I.A3.fam3.base3.v0.embedding y := by
    first
    | exact hH.h2g.1 h
    | exact (hH.h2g.2 I.A3.fam3.base3.μ0).1 h
  funext i
  have h2 := congrFun h1 i
  simp only [cpt] at h2
  exact I.A3.fam3.base3.v0.embedding.injective h2

theorem rowG_surj (t : T) : Function.Surjective (I.X.rowMat I.cg false t).mulVec :=
  (bij_of_map I.A3.fam3.base3.v0.embedding _ (by
    rw [CxData.rowMat, kMat_map _ (hH.ratMug t)]
    exact relMat_bij _ _ hH.h2g.1 (hH.h2g.2 t).1 (hH.h2g.2 t).2)).2

theorem epM_idem (hρ : I.PRho) (P : Subgroup G) (ψ : P →* Kˣ) : I.epM P ψ * I.epM P ψ = I.epM P ψ := by
  obtain ⟨h1, hm, -⟩ := hρ s hH
  letI : Fintype P := Fintype.ofFinite P
  have hmul : ∀ h k : P, ((((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)) * ((((ψ k)⁻¹ : Kˣ) : K) • I.ρf (k : G)) =
      (((ψ (h * k))⁻¹ : Kˣ) : K) • I.ρf ((h * k : P) : G) := by
    intro h k
    first
    | rw [smul_mul_smul_comm]
    | rw [smul_mul_smul]
    rw [← hm, Subgroup.coe_mul, map_mul, mul_inv, Units.val_mul]
  have hSS : (∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)) * (∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G)) =
      (Fintype.card P : K) • ∑ h : P, (((ψ h)⁻¹ : Kˣ) : K) • I.ρf (h : G) := by
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum, hmul]
    have e : ∀ h : P, ∑ k : P, (((ψ (h * k))⁻¹ : Kˣ) : K) • I.ρf ((h * k : P) : G) =
        ∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • I.ρf (k : G) :=
      fun h => Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun k => rfl)
    simp_rw [e]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul K]
  unfold epM
  first
  | rw [smul_mul_smul_comm, hSS, smul_smul]
  | rw [smul_mul_smul, hSS, smul_smul]
  congr 1
  have hne : (Fintype.card P : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Nat.card_eq_fintype_card]
  field_simp

theorem toRg_inj (t : T) : Function.Injective (I.cg.toR I.X.zs false t) :=
  BlockDat.toF_injective (I.A.fam.R t) (Lvl.full I.A.fam.X) (I.X.Z t)

theorem sub_g (t : T) (P : Subgroup G) (ψ : P →* Kˣ)
    (J : Matrix (Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((I.A.fam.R t).dZ (I.A.fam.lvl P ψ) (I.X.Z t))) K)
    (hJ : ∀ x, I.cg.toR I.X.zs false t (J *ᵥ x) = (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) x) :
    ∀ y ∈ (I.A.fam.R t).abelian₂ (I.A.fam.lvl P ψ) (I.X.Z t),
      J *ᵥ y ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t := by
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hy
  obtain ⟨f', hf', he⟩ := Sand.sub_toF (B := I.A.fam.R t) (hv0 := hH.ok.ok2.conj) (hOk := hH.ok.ok2.what₂ t)
    (hX := hH.ok.ok2.irr) (Z := I.X.Z t) (hZ := hZ_of hH t) (P := P) (ψ := ψ) f hf
  have hex : ∃ z ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t,
      I.cg.toR I.X.zs false t z =
        (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) ((I.A.fam.R t).Pq (I.A.fam.lvl P ψ) (I.X.Z t) *ᵥ f) :=
    ⟨_, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨f', hf', rfl⟩, he.symm⟩
  obtain ⟨z, hz, hze⟩ := hex
  have e : J *ᵥ ((I.A.fam.R t).Pq (I.A.fam.lvl P ψ) (I.X.Z t) *ᵥ f) = z := toRg_inj hH t (by rw [hJ, hze])
  rw [e]
  exact hz

theorem avg_g (hρ : I.PRho) (t : T) (P : Subgroup G) (ψ : P →* Kˣ)
    (J : Matrix (Fin ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).dQ t))
      (Fin ((I.A.fam.R t).dZ (I.A.fam.lvl P ψ) (I.X.Z t))) K)
    (hJ : ∀ x, I.cg.toR I.X.zs false t (J *ᵥ x) = (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) x) :
    ∀ y ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t,
      ∃ z ∈ (I.A.fam.R t).abelian₂ (I.A.fam.lvl P ψ) (I.X.Z t),
        (Nat.card P : K) • (I.epM P ψ *ᵥ (I.X.rowMat I.cg false t *ᵥ y)) = I.X.rowMat I.cg false t *ᵥ (J *ᵥ z) := by
  intro y hy
  obtain ⟨f, hf, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hy
  let _ : Fintype P := Fintype.ofFinite P
  obtain ⟨fb, hfb, he⟩ := Sand.avg_toF (B := I.A.fam.R t) (hv0 := hH.ok.ok2.conj) (hOk := hH.ok.ok2.what₂ t)
    (hX := hH.ok.ok2.irr) (Z := I.X.Z t) (hZ := hZ_of hH t) (P := P) (ψ := ψ) f hf
  have hex : ∃ z ∈ (I.A.fam.R t).abelian₂ (I.A.fam.lvl P ψ) (I.X.Z t),
      ∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • (I.A.fam.R t).r (k : G)
        (I.cg.toR I.X.zs false t ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq t *ᵥ f)) =
        (I.A.fam.R t).toF (I.A.fam.lvl P ψ) (I.X.Z t) z :=
    ⟨_, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨fb, hfb, rfl⟩, he⟩
  obtain ⟨z, hz, hze⟩ := hex
  refine ⟨z, hz, ?_⟩
  have hc : (Nat.card P : K) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := P)).ne'
  have hep : I.epM P ψ = (Nat.card P : K)⁻¹ • ∑ k : P, (((ψ k)⁻¹ : Kˣ) : K) • I.ρf (k : G) := rfl
  apply inj_g hH
  rw [key_g hH, hJ, ← hze, hep, Matrix.smul_mulVec, smul_smul, mul_inv_cancel₀ hc, one_smul,
    Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]
  erw [Sand.cpt_sum_smul]
  rw [map_sum]
  erw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  erw [map_smul, (hρ s hH).2.2 (k : G) (I.X.rowMat I.cg false t *ᵥ ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq t *ᵥ f)),
    key_g hH t ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq t *ᵥ f), LinearMap.map_smulₛₗ, map_smul]
  exact congrArg _ (hH.gequiv t k _).symm

theorem sub_b (hJt : I.PJt) (b : Bool) (t : T) :
    ∀ y ∈ (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).abelian₂ t,
      I.Jt b t *ᵥ y ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t := by
  cases b
  · exact sub_g hH t I.P0 I.ψ0 (I.Jt false t) (fun x => (hJt s hH false t).2.1 x)
  · exact sub_g hH t I.P1 I.ψ1 (I.Jt true t) (fun x => (hJt s hH true t).2.1 x)

theorem avg_b (hJt : I.PJt) (hρ : I.PRho) (b : Bool) (t : T) :
    ∀ y ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t,
      ∃ z ∈ (lv (faceOf3 I.A3 I.P0 I.ψ0 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) b).abelian₂ t,
        (Nat.card (I.lvP b) : K) • (I.epM (I.lvP b) (I.lvψ b) *ᵥ (I.X.rowMat I.cg false t *ᵥ y)) =
          I.X.rowMat I.cg false t *ᵥ (I.Jt b t *ᵥ z) := by
  cases b
  · exact avg_g hH hρ t I.P0 I.ψ0 (I.Jt false t) (fun x => (hJt s hH false t).2.1 x)
  · exact avg_g hH hρ t I.P1 I.ψ1 (I.Jt true t) (fun x => (hJt s hH true t).2.1 x)

end Prin

theorem pLat_of (_hJt : I.PJt) : I.PLat := by
  intro s hH
  have : Finite T := hH.ok.ok2.tup_fin
  exact Sand.glue_lattice I.A3.fam3.base3.μ0 I.X.μ
    (fun t => matLat (I.X.rowMat I.cg false t) ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ t))
    (fun t => GluingInclusion.matLat_lattice' _ (rowG_surj hH t) _
      (show Submodule.IsLattice K ((I.A.fam.R t).abelian₂ (Lvl.full I.A.fam.X) (I.X.Z t)) from
        BlockDat.Lam_lat hH.ok.ok2.conj (hH.ok.ok2.what₂ t) hH.ok.ok2.irr))

theorem pGLat_of (_hJt : I.PJt) (hρ : I.PRho) : I.PGLat := by
  intro s hH g x hx
  rw [mem_RRg] at hx ⊢
  intro w
  obtain ⟨c, hc, z, hz, hzx⟩ := hx w
  obtain ⟨f, hf, rfl⟩ := (exponent_index_lattice.mem_matLat _ _ _).mp hz
  obtain ⟨f', hf', he⟩ := Sand.act_toF (B := I.A.fam.R (I.X.μ w)) (hv0 := hH.ok.ok2.conj) (hOk := hH.ok.ok2.what₂ _)
    (hX := hH.ok.ok2.irr) (Z := I.X.Z (I.X.μ w)) (hZ := hZ_of hH _) g f hf
  have hex : ∃ z ∈ (lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).abelian₂ (I.X.μ w),
      (I.A.fam.R (I.X.μ w)).r g (I.cg.toR I.X.zs false (I.X.μ w)
        ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq (I.X.μ w) *ᵥ f)) =
        I.cg.toR I.X.zs false (I.X.μ w) z :=
    ⟨_, (exponent_index_lattice.mem_matLat _ _ _).mpr ⟨f', hf', rfl⟩, he⟩
  obtain ⟨z', hz', hze⟩ := hex
  refine ⟨c, hc, z', hz', ?_⟩
  rw [← exponent_index_lattice.mulVec_osmul, ← hzx]
  apply inj_g hH
  erw [key_g hH, (hρ s hH).2.2 g (I.X.rowMat I.cg false (I.X.μ w) *ᵥ ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq (I.X.μ w) *ᵥ f)),
    key_g hH (I.X.μ w) ((lv (faceOf3 I.A3 ⊥ 1 I.P1 I.ψ1 I.Dc I.Sp I.Zsc I.X.zs) false).Pq (I.X.μ w) *ᵥ f), ← hze]
  exact hH.gequiv _ g _

theorem pSand_of (hJt : I.PJt) (hJ : I.PJ) (hρ : I.PRho) (hR : I.PRange) : I.PSand := by
  intro s hH b
  refine ⟨fun x hx => ?_, fun y hy hyr => ?_⟩
  · rw [mem_RRb] at hx
    rw [mem_RRg]
    intro w
    obtain ⟨c, hc, z, hz, hzx⟩ := hx w
    refine ⟨c, hc, I.Jt b (I.X.μ w) *ᵥ z, sub_b hH hJt b _ z hz, ?_⟩
    exact ((hJt s hH b _).2.2 z).symm.trans
      ((congrArg (fun v => I.Jm b *ᵥ v) hzx).trans (exponent_index_lattice.mulVec_osmul _ _ _))
  · obtain ⟨z0, hz0⟩ := LinearMap.mem_range.mp hyr
    have hyr' := hyr
    rw [← hR s hH b] at hyr'
    obtain ⟨x0, hx0⟩ := LinearMap.mem_range.mp hyr'
    rw [Matrix.mulVecLin_apply] at hz0 hx0
    have hidem : I.epM (I.lvP b) (I.lvψ b) *ᵥ y = y := by
      rw [← hz0, Matrix.mulVec_mulVec, epM_idem hH hρ]
    refine ⟨((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • x0, ?_, by rw [exponent_index_lattice.mulVec_osmul, hx0]⟩
    rw [mem_RRg] at hy
    rw [mem_RRb]
    intro w
    obtain ⟨c, hc, z, hz, hzy⟩ := hy w
    obtain ⟨zb, hzb, he⟩ := avg_b hH hJt hρ b (I.X.μ w) z hz
    refine ⟨c, hc, zb, hzb, ?_⟩
    apply (hJ s hH b).2
    have h3 : (Nat.card (I.lvP b) : K) •
        (I.epM (I.lvP b) (I.lvψ b) *ᵥ (I.X.rowMat I.cg false (I.X.μ w) *ᵥ z)) =
        I.Jm b *ᵥ (c • (((Nat.card (I.lvP b) : ℕ) : 𝓞 K) • x0)) := by
      have h4 : I.epM (I.lvP b) (I.lvψ b) *ᵥ (I.X.rowMat I.cg false (I.X.μ w) *ᵥ z) = c • y :=
        (congrArg (fun v => I.epM (I.lvP b) (I.lvψ b) *ᵥ v) hzy).trans (by rw [exponent_index_lattice.mulVec_osmul, hidem])
      rw [h4]
      simp only [exponent_index_lattice.mulVec_osmul]
      rw [hx0, Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul (𝓞 K), smul_comm]
    exact ((hJt s hH b _).2.2 zb).trans (he.symm.trans h3)

end In3

end Formalism.IndefR.CxPass
