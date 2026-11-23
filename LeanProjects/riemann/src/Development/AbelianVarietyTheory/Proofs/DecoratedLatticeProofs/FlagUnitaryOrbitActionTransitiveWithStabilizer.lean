import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerBF
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentFourierJacobiGroupStructure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFramesSameGramOneUnitaryOrbitStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.OrbAct

variable {D : D7}

theorem exists_leftInv {m k : ℕ} (x : Matrix (Fin m) (Fin k) D.host.E) (hx : LinearIndependent D.host.E x.transpose) :
    ∃ L : Matrix (Fin k) (Fin m) D.host.E, L * x = 1 := by
  have hinj : Function.Injective x.mulVec := Matrix.mulVec_injective_iff.2 hx
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' x)
    (LinearMap.ker_eq_bot.2 fun a b h => hinj (by simpa only [Matrix.toLin'_apply] using h))
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h

section Block

variable {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ)

theorem blockX_spec {n : GA D V} (hn : n ∈ flagN d) :
    ∃ u ∈ UX D ρ, blockX d n = u.1 ∧ mt V n ⬝ d.jX = d.jX ⬝ u.1 := by
  obtain ⟨u, hu, b, c, rfl⟩ := ((flag_jacobi_structure D V V₀ ρ d).1 n).1 hn
  have h1 : mt V (d.levi u * (d.nB b * d.nC c)) ⬝ d.jX = d.jX ⬝ u.1 := by
    rw [mt_mul, mt_mul, Matrix.mul_assoc, Matrix.mul_assoc, d.nC_jX, d.nB_jX, d.levi_jX]
  refine ⟨u, hu, ?_, h1⟩
  rw [blockX, h1, ← Matrix.mul_assoc d.pX d.jX, d.pX_jX, Matrix.one_mul]

theorem mt_jX {n : GA D V} (hn : n ∈ flagN d) : mt V n ⬝ d.jX = d.jX ⬝ blockX d n := by
  obtain ⟨u, -, h1, h2⟩ := blockX_spec d hn
  rw [h2, h1]

theorem blockX_one : blockX d 1 = 1 := by rw [blockX, mt_one, Matrix.one_mul, d.pX_jX]

theorem blockX_mul {n n' : GA D V} (hn : n ∈ flagN d) (hn' : n' ∈ flagN d) :
    blockX d (n * n') = blockX d n ⬝ blockX d n' := by
  have h : mt V (n * n') ⬝ d.jX = d.jX ⬝ (blockX d n ⬝ blockX d n') := by
    rw [mt_mul, Matrix.mul_assoc, mt_jX d hn', ← Matrix.mul_assoc (mt V n) d.jX, mt_jX d hn, Matrix.mul_assoc]
  rw [blockX, h, ← Matrix.mul_assoc d.pX d.jX, d.pX_jX, Matrix.one_mul]

theorem blockX_rat {n : GA D V} (hn : n ∈ GQ V) : blockX d n ∈ ratMx D ρ ρ :=
  ratMx_mul (rat_mem d.qX) (ratMx_mul ((mem_GQ_iff V n).1 hn) (rat_mem d.e))

theorem cancel_blockX {n : GA D V} (hn : n ∈ flagN d) {m : ℕ} {y y' : Mx D m ρ}
    (h : y ⬝ blockX d n = y' ⬝ blockX d n) : y = y' := by
  have e : blockX d n ⬝ blockX d n⁻¹ = 1 := by
    rw [← blockX_mul d hn (inv_mem hn), mul_inv_cancel, blockX_one]
  calc y = y ⬝ (blockX d n ⬝ blockX d n⁻¹) := by rw [e, Matrix.mul_one]
    _ = y' ⬝ (blockX d n ⬝ blockX d n⁻¹) := by rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
    _ = y' := by rw [e, Matrix.mul_one]

variable {W : HSp D} {x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E}

theorem orb_ext {n : GA D V} (hn : n ∈ flagN d) {y y' : Orb W x₀}
    (h : (rat y.1 : Mx D W.rank ρ) ⬝ blockX d n = rat y'.1 ⬝ blockX d n) : y = y' :=
  Subtype.ext (rat_injective (cancel_blockX d hn h))

theorem exists_act (hx : IsBase W x₀) (γ : (NFlagQ V d.e).prod (GQ W)) (x : Orb W x₀) :
    ∃ x' ∈ Orb W x₀, (rat x' : Mx D W.rank ρ) ⬝ blockX d γ.1.1.1 = mt W γ.1.2 ⬝ rat x.1 := by
  have hγ := Subgroup.mem_prod.1 γ.2
  have hn : γ.1.1.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 (hγ.1 : γ.1.1 ∈ (GQ V).subgroupOf (NFlag V d.e))
  have hf : γ.1.1.1 ∈ flagN d := γ.1.1.2
  obtain ⟨x₁, hx₁, e₁⟩ := (GlobalTheory.T.rational_frames_same_gram_one_unitary_orbit D W ρ x₀ hx.1).2 γ.1.2 hγ.2 x.1 x.2
  obtain ⟨u, hu, hb, -⟩ := blockX_spec d (inv_mem hf)
  obtain ⟨v, hv⟩ := mem_ratMx.1 (blockX_rat d (inv_mem hn))
  obtain ⟨w, hw⟩ := mem_ratMx.1 (blockX_rat d hn)
  replace hv : (rat v : Mx D ρ ρ) = blockX d γ.1.1.1⁻¹ := hv
  replace hw : (rat w : Mx D ρ ρ) = blockX d γ.1.1.1 := hw
  have e2 : w * v = 1 := rat_injective (by
    rw [rat_mul, hv, hw, ← blockX_mul d hf (inv_mem hf), mul_inv_cancel, blockX_one, rat_one])
  refine ⟨x₁ * v, ⟨?_, ?_⟩, ?_⟩
  · apply Matrix.mulVec_injective_iff.1
    intro a b hab
    have hi : Function.Injective x₁.mulVec := Matrix.mulVec_injective_iff.2 hx₁.1
    have h1 : v *ᵥ a = v *ᵥ b := hi (by simpa only [Matrix.mulVec_mulVec] using hab)
    have h2 := congrArg (w *ᵥ ·) h1
    simpa only [Matrix.mulVec_mulVec, e2, Matrix.one_mulVec] using h2
  · apply rat_injective
    rw [show gramQ W (x₁ * v) = vᴴ * (gramQ W x₁ * v) by simp only [gramQ, conjTranspose_mul, Matrix.mul_assoc],
      hx₁.2, rat_mul, rat_mul, rat_conjTranspose, hv, hb]
    exact hx.2 u hu
  · rw [rat_mul, hv, Matrix.mul_assoc, ← blockX_mul d (inv_mem hf) hf, inv_mul_cancel, blockX_one, Matrix.mul_one, e₁]

def act (hx : IsBase W x₀) (γ : (NFlagQ V d.e).prod (GQ W)) (x : Orb W x₀) : Orb W x₀ :=
  ⟨Classical.choose (exists_act d hx γ x), (Classical.choose_spec (exists_act d hx γ x)).1⟩

theorem act_spec (hx : IsBase W x₀) (γ : (NFlagQ V d.e).prod (GQ W)) (x : Orb W x₀) :
    (rat (act d hx γ x).1 : Mx D W.rank ρ) ⬝ blockX d γ.1.1.1 = mt W γ.1.2 ⬝ rat x.1 :=
  (Classical.choose_spec (exists_act d hx γ x)).2

attribute [irreducible] act

def mulAct (hx : IsBase W x₀) : MulAction ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀) where
  smul := act d hx
  one_smul x := by
    refine orb_ext d (n := 1) (one_mem _) ((act_spec d hx 1 x).trans ?_)
    show mt W 1 ⬝ rat x.1 = rat x.1 ⬝ blockX d 1
    rw [mt_one, blockX_one, Matrix.one_mul, Matrix.mul_one]
  mul_smul γ δ x := by
    have hf : ∀ γ : (NFlagQ V d.e).prod (GQ W), γ.1.1.1 ∈ flagN d := fun γ => γ.1.1.2
    have h2 := act_spec d hx γ (act d hx δ x)
    have h3 := act_spec d hx δ x
    refine orb_ext d (hf (γ * δ)) ((act_spec d hx (γ * δ) x).trans ?_)
    change mt W (γ.1.2 * δ.1.2) ⬝ rat x.1 = rat (act d hx γ (act d hx δ x)).1 ⬝ blockX d (γ.1.1.1 * δ.1.1.1)
    rw [blockX_mul d (hf γ) (hf δ), ← Matrix.mul_assoc, h2, Matrix.mul_assoc, h3, mt_mul, Matrix.mul_assoc]

theorem smul_def (hx : IsBase W x₀) (γ : (NFlagQ V d.e).prod (GQ W)) (x : Orb W x₀) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ (mulAct d hx).toSMul) γ x = act d hx γ x := rfl

def base (hx : IsBase W x₀) : Orb W x₀ := ⟨x₀, hx.1, rfl⟩

theorem base_val (hx : IsBase W x₀) : (base hx).1 = x₀ := rfl

theorem act_base_iff (hx : IsBase W x₀) (γ : (NFlagQ V d.e).prod (GQ W)) :
    act d hx γ (base hx) = base hx ↔ (rat x₀ : Mx D W.rank ρ) ⬝ blockX d γ.1.1.1 = mt W γ.1.2 ⬝ rat x₀ := by
  constructor
  · intro h
    have h' := act_spec d hx γ (base hx)
    rw [h] at h'
    exact h'
  · intro h
    exact orb_ext d γ.1.1.2 ((act_spec d hx γ (base hx)).trans h.symm)

theorem transitive (hx : IsBase W x₀) (x : Orb W x₀) : ∃ γ : (NFlagQ V d.e).prod (GQ W), act d hx γ (base hx) = x := by
  obtain ⟨h, hh, e⟩ := (GlobalTheory.T.rational_frames_same_gram_one_unitary_orbit D W ρ x₀ hx.1).1 x.1 x.2
  refine ⟨⟨(1, h), Subgroup.mem_prod.2 ⟨one_mem _, hh⟩⟩, orb_ext d (n := 1) (one_mem _) ((act_spec d hx _ _).trans ?_)⟩
  show mt W h ⬝ rat x₀ = rat x.1 ⬝ blockX d 1
  rw [blockX_one, Matrix.mul_one, e]

theorem leftInv_rat (hx : IsBase W x₀) : ∃ L : Matrix (Fin ρ) (Fin W.rank) D.host.E,
    (rat L : Mx D ρ W.rank) ⬝ rat x₀ = 1 := by
  obtain ⟨L, hL⟩ := exists_leftInv x₀ hx.1
  exact ⟨L, by rw [← rat_mul, hL, rat_one]⟩

theorem stab_left (hx : IsBase W x₀) (n : NFlag V d.e) :
    (∃ γ : (NFlagQ V d.e).prod (GQ W), act d hx γ (base hx) = base hx ∧ γ.1 = (n, 1)) ↔ n.1 ∈ GQ V ⊓ radX d := by
  obtain ⟨L, hLa⟩ := leftInv_rat hx
  constructor
  · rintro ⟨γ, hγ, e'⟩
    have h1 := (act_base_iff d hx γ).1 hγ
    rw [show γ.1.1 = n from congrArg Prod.fst e', show γ.1.2 = 1 from congrArg Prod.snd e', mt_one,
      Matrix.one_mul] at h1
    have hB : blockX d n.1 = 1 :=
      calc blockX d n.1 = ((rat L : Mx D ρ W.rank) ⬝ rat x₀) ⬝ blockX d n.1 := by rw [hLa, Matrix.one_mul]
        _ = 1 := by rw [Matrix.mul_assoc, h1, hLa]
    have hG : n.1 ∈ GQ V := by
      rw [← show γ.1.1 = n from congrArg Prod.fst e']
      exact Subgroup.mem_subgroupOf.1 ((Subgroup.mem_prod.1 γ.2).1 : γ.1.1 ∈ (GQ V).subgroupOf (NFlag V d.e))
    have hfix : mt V n.1 ⬝ d.jX = d.jX := by rw [mt_jX d n.2, hB, Matrix.mul_one]
    have hR : n.1 ∈ radX d := Subgroup.mem_inf.2 ⟨n.2, (mem_fixer.2 hfix : n.1 ∈ fixer V d.jX)⟩
    exact Subgroup.mem_inf.2 ⟨hG, hR⟩
  · intro hn
    obtain ⟨hG, hR⟩ := Subgroup.mem_inf.1 hn
    have hB : blockX d n.1 = 1 := blockX_of_fix d (radX_le_stabX d hR)
    refine ⟨⟨(n, 1), Subgroup.mem_prod.2
      ⟨(Subgroup.mem_subgroupOf.2 hG : n ∈ (GQ V).subgroupOf (NFlag V d.e)), one_mem _⟩⟩, ?_, rfl⟩
    refine (act_base_iff d hx _).2 ?_
    show rat x₀ ⬝ blockX d n.1 = mt W 1 ⬝ rat x₀
    rw [hB, mt_one, Matrix.one_mul, Matrix.mul_one]

theorem stab_right (hx : IsBase W x₀) (h : GA D W) :
    (∃ γ : (NFlagQ V d.e).prod (GQ W), act d hx γ (base hx) = base hx ∧ γ.1.2 = h) ↔ h ∈ GQ W ⊓ Rgrp W (rat x₀) := by
  obtain ⟨L, hLa⟩ := leftInv_rat hx
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    have h1 := (act_base_iff d hx γ).1 hγ
    obtain ⟨u, hu, hb, -⟩ := blockX_spec d γ.1.1.2
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_prod.1 γ.2).2, u, hu, h1.symm.trans (by rw [hb])⟩
  · intro hh
    obtain ⟨hG, u, hu, hR⟩ := Subgroup.mem_inf.1 hh
    have hu1 : u.1 ∈ ratMx D ρ ρ := by
      have e : u.1 = (rat L : Mx D ρ W.rank) ⬝ (mt W h ⬝ rat x₀) := by
        rw [hR, ← Matrix.mul_assoc, hLa, Matrix.one_mul]
      rw [e]
      exact ratMx_mul (rat_mem L) (ratMx_mul ((mem_GQ_iff W h).1 hG) (rat_mem x₀))
    have hR' : mt W h⁻¹ ⬝ rat x₀ = rat x₀ ⬝ (u⁻¹).1 := by
      calc mt W h⁻¹ ⬝ rat x₀ = mt W h⁻¹ ⬝ (rat x₀ ⬝ u.1) ⬝ (u⁻¹).1 := by
            rw [Matrix.mul_assoc (mt W h⁻¹), Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.mul_one]
        _ = rat x₀ ⬝ (u⁻¹).1 := by rw [← hR, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hu2 : (u⁻¹).1 ∈ ratMx D ρ ρ := by
      have e : (u⁻¹).1 = (rat L : Mx D ρ W.rank) ⬝ (mt W h⁻¹ ⬝ rat x₀) := by
        rw [hR', ← Matrix.mul_assoc, hLa, Matrix.one_mul]
      rw [e]
      exact ratMx_mul (rat_mem L) (ratMx_mul ((mem_GQ_iff W h⁻¹).1 (inv_mem hG)) (rat_mem x₀))
    have hlevi : d.levi u ∈ flagN d := ((flag_jacobi_structure D V V₀ ρ d).1 _).2
      ⟨u, hu, 0, 0, by rw [d.nB_zero, d.nC_zero, mul_one, mul_one]⟩
    have hQ : d.levi u ∈ GQ V := d.levi_mem_GQ hu1 hu2
    refine ⟨⟨(⟨d.levi u, hlevi⟩, h), Subgroup.mem_prod.2
      ⟨(Subgroup.mem_subgroupOf.2 hQ : (⟨d.levi u, hlevi⟩ : NFlag V d.e) ∈ (GQ V).subgroupOf (NFlag V d.e)), hG⟩⟩,
      ?_, rfl⟩
    refine (act_base_iff d hx _).2 ?_
    show rat x₀ ⬝ blockX d (d.levi u) = mt W h ⬝ rat x₀
    rw [blockX_levi, hR]

end Block

theorem action_transitive_stabiliser : ∀ (D : D7) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ)
    (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (hx : IsBase W x₀),
    ∃ (_ : MulAction ((NFlagQ V d.e).prod (GQ W)) (Orb W x₀)) (y₀ : Orb W x₀), y₀.1 = x₀ ∧
      (∀ (γ : (NFlagQ V d.e).prod (GQ W)) (x : Orb W x₀),
        (rat (γ • x).1 : Mx D W.rank ρ) ⬝ blockX d γ.1.1.1 = mt W γ.1.2 ⬝ rat x.1) ∧
      (∀ x : Orb W x₀, ∃ γ : (NFlagQ V d.e).prod (GQ W), γ • y₀ = x) ∧
      ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)).comap (MonoidHom.inl _ _) =
        (GQ V ⊓ radX d).subgroupOf (flagN d) ∧
      ((MulAction.stabilizer ((NFlagQ V d.e).prod (GQ W)) y₀).map (Subgroup.subtype _)).map (MonoidHom.snd _ _) =
        GQ W ⊓ Rgrp W (rat x₀) := by
  intro D V V₀ W ρ d x₀ hx
  refine ⟨mulAct d hx, base hx, base_val hx, ?_, ?_, ?_, ?_⟩
  · intro γ x
    rw [smul_def]
    exact act_spec d hx γ x
  · intro x
    obtain ⟨γ, hγ⟩ := transitive d hx x
    exact ⟨γ, by rw [smul_def]; exact hγ⟩
  · ext n
    rw [Subgroup.mem_comap, Subgroup.mem_map, Subgroup.mem_subgroupOf, ← stab_left d hx n]
    constructor
    · rintro ⟨γ, hγ, e⟩
      exact ⟨γ, (hγ : act d hx γ (base hx) = base hx), e⟩
    · rintro ⟨γ, hγ, e⟩
      exact ⟨γ, (hγ : act d hx γ (base hx) = base hx), e⟩
  · ext h
    rw [← stab_right d hx h]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hp
      exact ⟨γ, (hγ : act d hx γ (base hx) = base hx), rfl⟩
    · rintro ⟨γ, hγ, rfl⟩
      exact Subgroup.mem_map.2 ⟨γ.1, Subgroup.mem_map.2 ⟨γ, (hγ : act d hx γ (base hx) = base hx), rfl⟩, rfl⟩

end GlobalTheory.OrbAct

end
