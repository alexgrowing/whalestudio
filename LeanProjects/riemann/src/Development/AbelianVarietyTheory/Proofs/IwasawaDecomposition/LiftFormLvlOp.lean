import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubOrthProjPerpMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslateLiftV
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.CenFrame
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CenTranslate

section Act
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem extV_act (hr : R.grp_red_L) (hj : R.models_jV) (hc : R.models_cV) (i : Fin D.R.m) (t : T0) (g : G)
    (κ : GA D (Vc D i)) (hκ : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ) (u : (A.fam.L i t).S.Forms)
    (h : GA D (Vc D i)) :
    R.extV i t (R.jV i t ((A.fam.L i t).r g u)) h =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • R.extV i t (R.jV i t u) (h * κ) := by
  have hT := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g u
  have hq : (finHom (Vc D i)).rangeRestrict κ ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    have h1 := hκ.2.1
    exact ⟨h1, trivial⟩
  let q : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩
  have hl : GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.LiftsTo (Vc D i) (R.βV i) (R.datVt i t) q (R.eG g) := hκ.2.2
  have e := hT.2 q hl ((finHom (Vc D i)).rangeRestrict h)
  have hk : (R.cV i).ρ κ⁻¹ = 1 := (hc i).1 _ (inv_mem hκ.1)
  have hρ : (R.cV i).ρ (h * κ)⁻¹ = (R.cV i).ρ h⁻¹ := by
    rw [mul_inv_rev, MonoidHom.map_mul, hk, one_mul]
  have hrr : (finHom (Vc D i)).rangeRestrict (h * κ) = (finHom (Vc D i)).rangeRestrict h * (q : Bridge.Gf (Vc D i)) := map_mul _ _ _
  show (R.cV i).ρ h⁻¹ ((R.HV i t).e (R.jV i t ((A.fam.L i t).r g u)) ((finHom (Vc D i)).rangeRestrict h)) =
      (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ •
        (R.cV i).ρ (h * κ)⁻¹ ((R.HV i t).e (R.jV i t u) ((finHom (Vc D i)).rangeRestrict (h * κ)))
  have hch : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch q : ℂˣ) : ℂ) :=
    congrArg Units.val ((congrArg (levFn (R.βV i) (flagL (R.datVt i t))) (finE_eq (Vc D i) κ)).trans
      (GlobalTheory.LiftEquivariance.ch_eq q).symm)
  refine (congrArg ((R.cV i).ρ h⁻¹) e).trans ?_
  refine (LinearMap.map_smul _ _ _).trans ?_
  exact congrArg₂ (fun (a : ℂ) w => a • w) ((Units.val_inv_eq_inv_val _).trans (congrArg (·⁻¹) hch.symm))
    (congrArg₂ (fun (f : Module.End ℂ (R.cV i).W) w => f w) hρ.symm (congrArg ((R.HV i t).e (R.jV i t u)) hrr.symm))
end Act

section Read
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A3.A Ks} {F : Face D A3.A} {X0 : BaseLevelRowSide D}

theorem liftForm_lvlOp (hOk : A3.A.fam.Ok 1) (i : Fin D.R.m) (t : T) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) :
    liftForm A3.A F.P0 F.ψ0 i t (((A3.A.fam.L i t).S.lvlOp (A3.A.fam.L i t).r (A3.A.fam.lvlA F.P0 F.ψ0).P
          (A3.A.fam.lvlA F.P0 F.ψ0).ψ a).mulVec x) =
      ∑ g, a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x) :=
  GlobalTheory.ClassSumIdentity.lvlE_lvlOp hOk.conj (A3.A.fam.L i t).S ((hOk.lifts i t).hpos _) (A3.A.fam.L i t).r (hOk.lifts i t).act
    _ _ a ha x

theorem read_rat (hB : R.BaseW F) (hOk : A3.A.fam.Ok 1) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd)
    (hC : CenRead Y cG) (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i))
    (hκ : ∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g))
    (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (a : MonoidAlgebra D.what₂.LL G) (ha : ∀ b, b * a = a * b)
    (hza : ∀ g, D.what₂.embLL (a.coeff g) = (z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g))
    (x : Fin (lDim D A3.A F.P0 F.ψ0 i t) → D.what₂.LL) (h : GA D (Vc D i)) :
    (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z
        (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x)))).1 h =
      ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
        (Y.IL.jMt (Y.tup t) ht i (D.what₂.jMt (Y.tup t) ((i : ℕ) + 1) (Y.eMt i t x))).1 (h * κ g) := by
  have e1 := congrArg (fun y => (Y.IL.jMt (Y.tup t) ht i y).1 h) (hC i t z a hza x)
  refine e1.trans ?_
  refine (congrFun (Y.mtRead i t ht _) h).trans ?_
  refine Eq.trans ?_ (Finset.sum_congr rfl fun g _ =>
    congrArg (fun w => ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) *
        (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • w) (congrFun (Y.mtRead i t ht x) (h * κ g)).symm)
  have e2 := liftForm_lvlOp (F := F) hOk i t a ha x
  refine (congrArg (fun v => R.extV i t (R.jV i t v) h) e2).trans ?_
  have e3 := map_sum (R.jV i t) (fun g => a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)) Finset.univ
  have e4 := map_sum (R.extV i t) (fun g => (R.jV i t) (a.coeff g • (A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))) Finset.univ
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e3).trans e4)).trans ?_
  refine (Finset.sum_apply h _ _).trans ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  have e5 := map_smulₛₗ (R.jV i t) (a.coeff g) ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x))
  have e6 := LinearMap.map_smul (R.extV i t) (D.what₂.embLL (a.coeff g)) (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))
  refine (congrArg (fun f => f h) ((congrArg (R.extV i t) e5).trans e6)).trans ?_
  refine (Pi.smul_apply (D.what₂.embLL (a.coeff g)) (R.extV i t (R.jV i t ((A3.A.fam.L i t).r g (liftForm A3.A F.P0 F.ψ0 i t x)))) h).trans ?_
  have e7 := extV_act hB.grp.red_L hB.models.jV hB.models.cV i t g (κ g) (hκ g) (liftForm A3.A F.P0 F.ψ0 i t x) h
  refine (congrArg (fun w => D.what₂.embLL (a.coeff g) • w) e7).trans ?_
  refine (smul_smul _ _ _).trans ?_
  exact congrArg (fun c : ℂ => (c * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) •
    R.extV i t (R.jV i t (liftForm A3.A F.P0 F.ψ0 i t x)) (h * κ g)) (hza g)

end Read

theorem sum_reindex {G H W : Type} [Group G] [Fintype G] [Group H] [Fintype H] [AddCommGroup W] [Module ℂ W] (e : G ≃* H)
    (c : H → ℂ) (ch : G → ℂ) (w : G → W) :
    ∑ g, (c (e g) * ch g) • w g = ∑ g₀, c g₀ • (ch (e.symm g₀) • w (e.symm g₀)) :=
  Fintype.sum_equiv e.toEquiv _ _ fun g => by simp [smul_smul]

theorem main : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A3.A Ks) (F : Face D A3.A) (X0 : BaseLevelRowSide D) (Y : R3.Read (A3 := A3) R F X0) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.BaseW F → A3.A.fam.Ok 1 → CenRead Y cG → ∀ (i : Fin D.R.m) (t : T) (ht : Used0 D (Y.tup t)) (κ : G → GA D (Vc D i)), (∀ g, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) (κ g)) → ∀ (z : Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) (y : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)) (h : GA D (Vc D i)), (Y.IL.jMt (Y.tup t) ht i (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z y)).1 h = ∑ g : G, ((z : MonoidAlgebra ℂ (G0g D.nd)).coeff ((R.eG.trans cG) g) * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹) • (Y.IL.jMt (Y.tup t) ht i y).1 (h * κ g) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F X0 Y cG hB hOk hC i t ht κ hκ z y h
  letI : Fintype (G0g D.nd) := Fintype.ofEquiv G (R.eG.trans cG).toEquiv
  let ad : GA D (Vc D i) → D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W := fun h' =>
    { toFun := fun y' => (Y.IL.jMt (Y.tup t) ht i y').1 h'
      map_add' := fun y₁ y₂ => by rw [map_add]; rfl
      map_smul' := fun c y₁ => by rw [map_smul]; rfl }
  let ch : G → ℂ := fun g => (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) (κ g))⁻¹
  have key : ∀ (g₁ : G0g D.nd) (y' : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1)),
      ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩ y') =
        ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g) y' := by
    intro g₁
    have tie : ∀ g, D.what₂.embLL ((GlobalTheory.CenLocAt.avgK D.what₂.LL ((R.eG.trans cG).symm g₁)).coeff g) =
        (GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) := fun g => by
      rw [GlobalTheory.CenLocAt.avgK_coeff D.what₂.embLL (R.eG.trans cG), MulEquiv.apply_symm_apply]
    let F1 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      (ad h).comp (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) ⟨GlobalTheory.CenLocAt.avgC g₁, GlobalTheory.CenLocAt.avgC_mem g₁⟩)
    let F2 : D.what₂.Mt (Y.tup t) ((i : ℕ) + 1) →ₗ[ℂ] (R.cV i).W :=
      ∑ g : G, ((GlobalTheory.CenLocAt.avgC g₁).coeff ((R.eG.trans cG) g) * ch g) • ad (h * κ g)
    have hb := (D.what₂.jMt_basis (Y.tup t) ((i : ℕ) + 1)
      (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)))).2
    have hF : F1 = F2 := by
      refine LinearMap.ext_on_range hb (fun b => ?_)
      obtain ⟨x', hx'⟩ := (Y.eMt i t).surjective (Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL (Y.tup t) ((i : ℕ) + 1)) b)
      rw [← hx']
      refine (read_rat hB hOk Y cG hC i t ht κ hκ ⟨_, GlobalTheory.CenLocAt.avgC_mem g₁⟩ _ (GlobalTheory.CenLocAt.avgK_comm _ _) tie x' h).trans ?_
      simp only [F2, LinearMap.sum_apply, LinearMap.smul_apply]
      rfl
    intro y'
    have := LinearMap.congr_fun hF y'
    simpa only [F1, F2, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply] using this
  let Φ : ↥(Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) →ₗ[ℂ] (R.cV i).W :=
    { toFun := fun z' => ad h (D.ntypes.cenMt (Y.tup t) ((i : ℕ) + 1) z' y)
      map_add' := fun z₁ z₂ => by simp only [map_add, LinearMap.add_apply]
      map_smul' := fun c z₁ => by simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hl := GlobalTheory.CenLocAt.lin_center Φ (fun g₀ => ch ((R.eG.trans cG).symm g₀) • ad (h * κ ((R.eG.trans cG).symm g₀)) y)
    (fun g₁ => (key g₁ y).trans (sum_reindex _ _ _ _)) z
  exact hl.trans (sum_reindex (R.eG.trans cG) _ ch (fun g => ad (h * κ g) y)).symm

end GlobalTheory.CenTranslate
