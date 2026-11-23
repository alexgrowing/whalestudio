import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatPIffMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinatesModPrimeSelfDualStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDetOfMemSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardLatticeQuotientHalfLevel

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares GlobalTheory.ShareOn

open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section
namespace GlobalTheory.ShareOn.UnipLevel

theorem pow_apply_eq_zero_of_strict {K : Type} [CommRing K] {n : ℕ} (S : Matrix (Fin n) (Fin n) K)
    (hS : ∀ a b : Fin n, b ≤ a → S a b = 0) (m : ℕ) :
    ∀ a b : Fin n, (b : ℕ) < a + m → (S ^ m) a b = 0 := by
  induction m with
  | zero =>
    intro a b h
    rw [pow_zero, Matrix.one_apply, if_neg]
    intro hab
    rw [hab] at h
    omega
  | succ m ih =>
    intro a b h
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : b ≤ j
    · rw [hS j b hj, mul_zero]
    · have hj' : (j : ℕ) < a + m := by
        have : (j : ℕ) < b := Fin.lt_def.1 (not_le.1 hj)
        omega
      rw [ih a j hj', zero_mul]

end GlobalTheory.ShareOn.UnipLevel
namespace GlobalTheory.ShareOn.UnipLevel

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem levUnip_mod_place : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (r : TwoRuns p.T p.P.Gp),
    RunsOk (fw2 p) r → ∀ (i : Fin D.R.m) (u : p.P.Gp) (k : Fin 2) (v : D.nd.PlG k),
    Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) →
    ∀ x : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l,
      (((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ D.R.r) x ∈
        ((D.naut.plGw k v).asIdeal • ⊤ : Submodule (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p r hr i u k v hU x
  classical
  obtain ⟨v'⟩ := GlobalTheory.ShareOn.nonempty_place D
  have hlev : Formalism.IndefR.FWT.LevIs (R2 p) i (Formalism.IndefR.FWT.iotaW p.T i) p.T.Q.l.M (Mfr p.T.Q.l)
      (fun g => liftLa (r.lev i g)) := hr.level v' i
  have hL := hr.laws v'
  have hι : LatEmb (Wc D i) (Formalism.IndefR.FWT.iotaW p.T i) := GlobalTheory.TraceLattice.latEmb_iotaW hL i
  have hβ : IsSDFrame (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) 1 := p.charW.base.lev.βW i
  obtain ⟨plg, iso, hplg, -, -, hG⟩ := p.grpRecPin
  have hrk : D.R.r = (p.T.Q.Dw ((i : ℕ) + 1)).p + (p.T.Q.Dw ((i : ℕ) + 1)).q :=
    (hL.j.unf _ ⟨Nat.le_add_left _ _, i.2⟩ _ (r.used v').full.toCore.good_σ₀).1
  set PPs := plg ⟨k, v⟩ with hPPs
  obtain ⟨φ, hφs, hφk⟩ := GlobalTheory.T.lattice_coordinates_mod_prime_selfDual_stabilizer D (Wc D i) ((R2 p).βW i) ((R2 p).ΛW i) hβ _ _ hι PPs.1
  obtain ⟨κ, hκ, hκa⟩ := hlev u
  have hMbP : p.T.Q.l.Mb ≤ PPs.1.asIdeal := by
    rw [hr.half]
    exact Ideal.prod_le_inf.trans (Finset.inf_le PPs.2)
  have hM : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PPs.1.asIdeal := hMbP (GlobalTheory.LevDesc.natCast_M_mem _)
  have hSt : Lev.finE (Wc D i) κ ∈ St ((R2 p).βW i) := parLev_St hκ.2.1
  have hkill : ∀ c ∈ PPs.1.asIdeal, ∀ y, φ (c • y) = 0 := by
    intro c hc y
    rw [map_smul]
    funext j
    rw [Pi.smul_apply, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 hc, zero_mul]
  have hcop : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  obtain ⟨c₁, hc₁, w, hw, hcw⟩ := Submodule.mem_sup.1 (hcop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ p.T.Q.l.Mb ⊔ Mfr p.T.Q.l)
  set f := liftLa (r.lev i u) with hf
  set N : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP PPs.1) :=
    (redFn ((R2 p).βW i) PPs.1 (Lev.finE (Wc D i) κ)).1 with hN
  have hfφ : ∀ a, φ (f a) = N *ᵥ φ a := by
    intro a
    have ha : a = c₁ • a + w • a := by rw [← add_smul, hcw, one_smul]
    have h1 := hφk κ hSt p.T.Q.l.M hM (w • a) (f (w • a)) (hκa (w • a) (Submodule.smul_mem_smul hw Submodule.mem_top))
    have h2 : φ (w • a) = φ a := by
      conv_rhs => rw [ha]
      rw [map_add, hkill c₁ (hMbP hc₁), zero_add]
    have h3 : φ (f a) = φ (f (w • a)) := by
      conv_lhs => rw [ha]
      rw [map_add, map_add, map_smul, hkill c₁ (hMbP hc₁), zero_add]
    rw [h3, h1, h2]
  have hrank : (Wc D i).rank = D.R.r := Formalism.IndefR.FWT.rank_Wc i
  have h5 : (R2 p).eG u PPs = upperLeftBlock ((R2 p).datWp i (R2 p).triv).hr (redFn ((R2 p).βW i) PPs.1 (Lev.finE (Wc D i) κ)) :=
    (congrFun hκ.2.2 PPs).symm
  have h6 := upper_block_val_submatrix ((R2 p).datWp i (R2 p).triv).hr (blockTri_blkOf_le _ _ (parLev_g hκ.2.1 PPs.2))
  have h7 : (R2 p).eG u PPs = Formalism.UG.bc (iso ⟨k, v⟩ : ZMod (D.host.g k) →+* kP PPs.1) ((p.R.eG.trans p.cG) u ⟨k, v⟩) :=
    hG u ⟨k, v⟩
  rw [← h5, h7] at h6
  have hsub : ∀ a' b' : Fin D.R.r, N (Fin.castLE ((R2 p).datWp i (R2 p).triv).hr a') (Fin.castLE ((R2 p).datWp i (R2 p).triv).hr b') =
      iso ⟨k, v⟩ ((((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k))) a' b') := by
    intro a' b'
    have := congrFun (congrFun h6 a') b'
    exact this.symm
  have hstrict : ∀ a b : Fin (Wc D i).rank, b ≤ a → (N - 1) a b = 0 := by
    intro a b hab
    have ha' : (a : ℕ) < D.R.r := hrank ▸ a.2
    have hb' : (b : ℕ) < D.R.r := hrank ▸ b.2
    have e1 : N a b = iso ⟨k, v⟩ ((((p.R.eG.trans p.cG) u ⟨k, v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k)))
        ⟨a, ha'⟩ ⟨b, hb'⟩) := hsub ⟨a, ha'⟩ ⟨b, hb'⟩
    rw [Matrix.sub_apply, e1]
    rcases lt_or_eq_of_le hab with h | h
    · rw [(hU ⟨a, ha'⟩ ⟨b, hb'⟩).1 h, map_zero, Matrix.one_apply_ne (ne_of_gt h), sub_zero]
    · have hab' : (⟨a, ha'⟩ : Fin D.R.r) = ⟨b, hb'⟩ := by
        ext; show (a : ℕ) = b; rw [h]
      rw [(hU ⟨a, ha'⟩ ⟨b, hb'⟩).2 hab', map_one, h, Matrix.one_apply_eq, sub_self]
  have hnil : (N - 1) ^ D.R.r = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    exact pow_apply_eq_zero_of_strict _ hstrict D.R.r a b (by have := b.2; omega)
  have hpow : ∀ (m : ℕ) a, φ (((f - LinearMap.id : Module.End (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ^ m) a) = ((N - 1) ^ m) *ᵥ φ a := by
    intro m
    induction m with
    | zero => intro a; rw [pow_zero, pow_zero, Module.End.one_apply, Matrix.one_mulVec]
    | succ m ih =>
      intro a
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, ← Matrix.mulVec_mulVec, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, hfφ, Matrix.sub_mulVec, Matrix.one_mulVec]
  have hker : ∀ y, φ y = 0 → y ∈ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
    intro y hy
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    haveI hfin : Finite (kP PPs.1) := Finite.of_equiv _ (iso ⟨k, v⟩).toEquiv
    haveI : Finite (𝓞 D.host.E ⧸ PPs.1.asIdeal) := hfin
    haveI := (p.T.Q.Dw ((i : ℕ) + 1)).fin
    haveI := (p.T.Q.Dw ((i : ℕ) + 1)).proj
    have hle : PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ≤ LinearMap.ker φ := by
      rw [Submodule.smul_le]
      intro c hc z _
      exact hkill c hc z
    let ψ := (PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).liftQ φ hle
    have hψs : Function.Surjective ψ := by
      intro z
      obtain ⟨y', rfl⟩ := hφs z
      exact ⟨Submodule.Quotient.mk y', rfl⟩
    have hc0 : Nat.card (kP PPs.1) ≠ 0 := Nat.card_pos.ne'
    have hN1 : Nat.card ((p.T.Q.Dw ((i : ℕ) + 1)).La ⧸ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) =
        Nat.card (kP PPs.1) ^ (Wc D i).rank := by
      rw [GlobalTheory.natCard_quot_smul_top_of_projective, (p.T.Q.Dw ((i : ℕ) + 1)).rank, ← hrk, hrank]
    have hN2 : Nat.card (Fin (Wc D i).rank → kP PPs.1) = Nat.card (kP PPs.1) ^ (Wc D i).rank := by
      rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
    haveI : Finite ((p.T.Q.Dw ((i : ℕ) + 1)).La ⧸ PPs.1.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) :=
      Nat.finite_of_card_ne_zero (by rw [hN1]; exact pow_ne_zero _ hc0)
    have hb := hψs.bijective_of_nat_card_le (by rw [hN1, hN2])
    have h0 : ψ (Submodule.Quotient.mk y) = ψ 0 := by
      rw [map_zero]
      exact hy
    exact (Submodule.Quotient.mk_eq_zero _).1 (hb.1 h0)
  have hmk : ∀ (m : ℕ) a, ((((r.lev i u).toLinearMap - LinearMap.id : Module.End (𝓞 D.host.E) (LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l)) ^ m)
      ((p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).mkQ a)) =
      (p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)).mkQ
        (((f - LinearMap.id : Module.End (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) ^ m) a) := by
    intro m
    induction m with
    | zero => intro a; rfl
    | succ m ih =>
      intro a
      rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, hf, ← liftLa_spec,
        ← map_sub, ← hf, ih, pow_succ, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.id_apply]
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hP : ((plg ⟨k, v⟩ : ↥p.R.Pg) : Pl D.host.E) = D.naut.plGw k v := hplg ⟨k, v⟩
  rw [← hP, ← hPPs]
  have hx := hmk D.R.r a
  rw [Submodule.mkQ_apply] at hx
  rw [hx]
  refine GlobalTheory.LevDesc.map_mem_smul_top _ (hker _ ?_)
  rw [hpow, hnil, Matrix.zero_mulVec]

end GlobalTheory.ShareOn.UnipLevel

end
