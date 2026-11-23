import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.CenLocAt

def avgC {G : Type} [Group G] [Fintype G] (g : G) : MonoidAlgebra ℂ G :=
  ((Fintype.card G : ℂ)⁻¹) • ∑ h : G, MonoidAlgebra.of ℂ G (h * g * h⁻¹)

theorem center_eq_sum {G : Type} [Group G] [Fintype G] (z : MonoidAlgebra ℂ G)
    (hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G)) : z = ∑ g : G, z.coeff g • avgC g := by
  rw [Subalgebra.mem_center_iff] at hz
  have h1 : ∀ h : G, MonoidAlgebra.of ℂ G h * z * MonoidAlgebra.of ℂ G h⁻¹ = z := by
    intro h
    rw [hz, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have h2 : z = ∑ g : G, z.coeff g • MonoidAlgebra.of ℂ G g := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single z]
    rw [Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single']
  have hc : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  calc z = (Fintype.card G : ℂ)⁻¹ • ∑ h : G, MonoidAlgebra.of ℂ G h * z * MonoidAlgebra.of ℂ G h⁻¹ := by
        simp only [h1, Finset.sum_const, Finset.card_univ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    _ = ∑ g : G, z.coeff g • avgC g := by
        conv_lhs => rw [h2]
        simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc, avgC, Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
        rw [← map_mul, ← map_mul, smul_comm]

theorem avgC_mem {G : Type} [Group G] [Fintype G] (g : G) : avgC g ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ G) := by
  rw [Subalgebra.mem_center_iff]
  intro b
  induction b using MonoidAlgebra.induction_on with
  | of x =>
    simp only [avgC, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun h => by simp [mul_assoc]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

def avgK (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g : G) : MonoidAlgebra K G :=
  ((Fintype.card G : K)⁻¹) • ∑ h : G, MonoidAlgebra.of K G (h * g * h⁻¹)

theorem avgK_coeff {K : Type} [Field K] {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H] (σ : K →+* ℂ) (e : G ≃* H)
    (g y : G) : σ ((avgK K g).coeff y) = (avgC (e g)).coeff (e y) := by
  simp only [avgK, avgC, MonoidAlgebra.of_apply]
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.single_apply, smul_eq_mul, map_mul, map_inv₀,
    map_natCast, map_sum, apply_ite, map_one, map_zero]
  rw [Fintype.card_congr e.toEquiv]
  congr 1
  refine Fintype.sum_equiv e.toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_mul, ← map_inv]
  classical
  rw [Finsupp.single_apply, Finsupp.single_apply]
  by_cases hy : h * g * h⁻¹ = y
  · rw [if_pos hy, if_pos (congrArg e hy), map_one]
  · rw [if_neg hy, if_neg (fun h' => hy (e.injective h')), map_zero]

theorem lin_center {G W : Type} [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
    (Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G)) →ₗ[ℂ] W) (v : G → W)
    (h : ∀ g₁, Φ ⟨avgC g₁, avgC_mem g₁⟩ = ∑ g₀, (avgC g₁).coeff g₀ • v g₀)
    (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) :
    Φ z = ∑ g₀, (z : MonoidAlgebra ℂ G).coeff g₀ • v g₀ := by
  have hz : z = ∑ g₁, (z : MonoidAlgebra ℂ G).coeff g₁ •
      (⟨avgC g₁, avgC_mem g₁⟩ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ G))) := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [SetLike.val_smul]
    exact center_eq_sum _ z.2
  conv_lhs => rw [hz]
  rw [map_sum]
  simp only [map_smul, h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g₀ _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [center_eq_sum _ z.2]
  simp [MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_smul, Finsupp.coe_finset_sum, Finset.sum_apply]

theorem avgK_comm (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g : G) (b : MonoidAlgebra K G) :
    b * avgK K g = avgK K g * b := by
  induction b using MonoidAlgebra.induction_on with
  | of x =>
    simp only [avgK, mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, ← map_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulLeft x) _ _ fun h => by simp [mul_assoc]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem avgK_conj (K : Type) [Field K] {G : Type} [Group G] [Fintype G] (g c y : G) :
    (avgK K g).coeff (c * y * c⁻¹) = (avgK K g).coeff y := by
  classical
  simp only [avgK, MonoidAlgebra.of_apply]
  simp only [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
    Finsupp.smul_apply, Finsupp.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine (Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun h => ?_).symm
  rw [Finsupp.single_apply, Finsupp.single_apply]
  refine if_congr ⟨fun e => ?_, fun e => ?_⟩ rfl rfl
  · rw [← e]; simp [mul_assoc]
  · have e' : c * (h * g * h⁻¹) * c⁻¹ = c * y * c⁻¹ := by rw [← e]; simp [mul_assoc]
    exact mul_left_cancel (mul_right_cancel e')

theorem actSum_apply (D : D7) {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E n)
    (z : MonoidAlgebra ℂ (G0g D.nd)) (f : Formalism.AUTREP.GAf D.host.E n → W) (g : Formalism.AUTREP.GAf D.host.E n) :
    GlobalTheory.PendOf.actSum D L z f g = ∑ g₀ : G0g D.nd, z.coeff g₀ • f (g * L g₀) := by
  unfold GlobalTheory.PendOf.actSum
  rw [Finsupp.sum_fintype _ _ (by intros; simp)]
  simp only [Finset.sum_apply, Pi.smul_apply]
  rfl

section Rows

open Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.RecTie

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)

def ratForm (k : Fin D.R.m) (s : T) (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) :=
  D.what₂.jMt (Y.tup s) ((k : ℕ) + 1) (Y.eMt k s x)

variable (F) in

def lvlAct (k : Fin D.R.m) (s : T) (a : MonoidAlgebra D.what₂.LL G) (x : Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL) :
    Fin (lDim D A3.A F.lv2.P0 F.lv2.ψ0 k s) → D.what₂.LL :=
  ((A3.A.fam.L k s).S.lvlOp (A3.A.fam.L k s).r (A3.A.fam.lvlA F.lv2.P0 F.lv2.ψ0).P (A3.A.fam.lvlA F.lv2.P0 F.lv2.ψ0).ψ a).mulVec x

def adForm (μ : D.what₂.Tup) (h : Used0 D μ) (k : Fin D.R.m) :
    D.what₂.Mt μ ((k : ℕ) + 1) →ₗ[ℂ] (GA D (Vc D k) → (R.cV k).W) where
  toFun x := (Y.IL.jMt μ h k x).1
  map_add' x y := by rw [map_add]; rfl
  map_smul' c x := by rw [map_smul]; rfl

def CenRat : Prop :=
  ∀ (s : T) (k : Fin D.R.m) (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (a : MonoidAlgebra D.what₂.LL G),
    (∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g)) →
    ∀ x, D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) z (ratForm Y k s x) = ratForm Y k s (lvlAct F k s a x)

def ActRead : Prop :=
  ∀ (s : T) (h : Used0 D (Y.tup s)) (k : Fin D.R.m) (a : MonoidAlgebra D.what₂.LL G), (∀ b, b * a = a * b) →
    ∀ κ : G → GA D (Vc D k), (∀ g, Lev.IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (κ g)) →
    ∀ x y, adForm Y (Y.tup s) h k (ratForm Y k s (lvlAct F k s a x)) y =
      ∑ g : G, (D.what₂.embLL (a.coeff g) * (Lev.levChi (Vc D k) (R.βV k) (Lev.flagL (R.datVt k s)) (κ g))⁻¹) •
        adForm Y (Y.tup s) h k (ratForm Y k s x) (y * κ g)

def FrameAt (k : Fin D.R.m) (P : principalLevelFrame.RowPsi (Vc D k) D.R.nV) (s : T) : Prop :=
  ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
    (Nontrivial (D.what₂.Mt (Y.tup s) ((k : ℕ) + 1)) → ∃ c : G, ∀ g : G,
      Lev.IsLevelLift (Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
      Lev.levChi (Vc D k) (R.βV k) (Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1)

set_option maxHeartbeats 1000000 in

theorem cenLoc_of (M : MtFam D) (ad : MtAd Y M) (h1 : CenRat Y cG) (h2 : ActRead Y)
    (h3 : ∀ (i : D.nd.Loc) (s : T) (k : Fin D.R.m), Y.tup s = D.nd.mu i → FrameAt Y cG k (ad.PV k) s) : CenLoc D M := by
  intro i
  suffices H : ∀ μ, Used0 D μ → ∀ (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ D.R.m),
      (∀ (s : T) (k : Fin D.R.m), Y.tup s = μ → FrameAt Y cG k (ad.PV k) s) →
      ∃ L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV, GlobalTheory.PendOf.IsTypeGroupBlockLift D D.R.nV L ∧
        ∀ (z : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))) (x : D.what₂.Mt μ j),
          (M μ j hj1 hj2).real (D.ntypes.cenMt μ j z x) =
            GlobalTheory.PendOf.actSum D L (z : MonoidAlgebra ℂ (G0g D.nd)) ((M μ j hj1 hj2).real x) from
    H _ (Model.used_loc i) _ (D.nd.j_range i).1 (D.nd.j_range i).2 (h3 i)
  intro μ hμ j hj1 hj2 h3
  obtain ⟨k, rfl⟩ : ∃ k : Fin D.R.m, j = (k : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp; omega⟩
  obtain ⟨s, rfl⟩ : ∃ s, Y.tup s = μ := ⟨_, Y.tupTie μ hμ⟩
  obtain ⟨L, hL, hc⟩ := h3 s k rfl
  refine ⟨L, hL, fun z x => funext fun g => ?_⟩
  rw [actSum_apply]
  rcases subsingleton_or_nontrivial (D.what₂.Mt (Y.tup s) ((k : ℕ) + 1)) with h0 | h0
  · rw [Subsingleton.elim x 0]; simp
  obtain ⟨c, hc⟩ := hc h0
  have key : ∀ g₁ : G0g D.nd,
      adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩ x) ((ad.PV k).ψ g) =
        ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k x ((ad.PV k).ψ (g * L g₀)) := by
    intro g₁
    have tie : ∀ y, D.what₂.embLL ((avgK D.what₂.LL ((R.eG.trans cG).symm g₁)).coeff y) = (avgC g₁).coeff ((R.eG.trans cG) y) :=
      fun y => by rw [avgK_coeff D.what₂.embLL (R.eG.trans cG), MulEquiv.apply_symm_apply]
    let F1 : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) →ₗ[ℂ] (R.cV k).W :=
      (LinearMap.proj ((ad.PV k).ψ g)).comp ((adForm Y (Y.tup s) hμ k).comp
        (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩))
    let F2 : D.what₂.Mt (Y.tup s) ((k : ℕ) + 1) →ₗ[ℂ] (R.cV k).W :=
      { toFun := fun y => ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k y ((ad.PV k).ψ (g * L g₀))
        map_add' := fun y y' => by simp only [map_add, Pi.add_apply, smul_add, Finset.sum_add_distrib]
        map_smul' := fun c y => by
          simp only [map_smul, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun _ _ => smul_comm _ _ _ }
    have hb := (D.what₂.jMt_basis (Y.tup s) ((k : ℕ) + 1)
      (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup s) ((k : ℕ) + 1)))).2
    have hF : F1 = F2 := by
      refine LinearMap.ext_on_range hb (fun b => ?_)
      obtain ⟨x', hx'⟩ := (Y.eMt k s).surjective (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup s) ((k : ℕ) + 1)) b)
      rw [← hx']
      show adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) ⟨avgC g₁, avgC_mem g₁⟩ (ratForm Y k s x'))
        ((ad.PV k).ψ g) = ∑ g₀ : G0g D.nd, (avgC g₁).coeff g₀ • adForm Y (Y.tup s) hμ k (ratForm Y k s x') ((ad.PV k).ψ (g * L g₀))
      rw [h1 s k ⟨avgC g₁, avgC_mem g₁⟩ _ tie x', h2 s hμ k _ (avgK_comm _ _) _ (fun y => (hc y).1) x']
      refine Fintype.sum_equiv ((MulAut.conj c).toEquiv.trans (R.eG.trans cG).toEquiv) _ _ fun y => ?_
      rw [(hc y).2, inv_one, mul_one, ← avgK_conj _ _ c y, tie, ← map_mul]
      rfl
    exact LinearMap.congr_fun hF x
  apply (ad.eW _ hμ k).injective
  rw [ad.read, map_sum]
  let Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₗ[ℂ] (R.cV k).W :=
    { toFun := fun z' => adForm Y (Y.tup s) hμ k (D.ntypes.cenMt (Y.tup s) ((k : ℕ) + 1) z' x) ((ad.PV k).ψ g)
      map_add' := fun y y' => by simp only [map_add, LinearMap.add_apply, Pi.add_apply]
      map_smul' := fun c y => by simp only [map_smul, LinearMap.smul_apply, Pi.smul_apply, RingHom.id_apply] }
  refine (lin_center Φ (fun g₀ => adForm Y (Y.tup s) hμ k x ((ad.PV k).ψ (g * L g₀))) key z).trans ?_
  refine Finset.sum_congr rfl fun g₀ _ => ?_
  rw [map_smul, ad.read]
  rfl

end Rows

end GlobalTheory.CenLocAt

end
