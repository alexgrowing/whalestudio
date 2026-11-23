import Formalism.LocalToGlobal.ProjectiveLattices.CoreAt
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFormsFiniteDimensionalOf

noncomputable section

namespace Formalism.L2.Pj.V3

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open MeasureTheory
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct
open Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Rows

variable {D : D7}

structure PkgRows (hN : N1c) (Q : Par D) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q) (hI : InfPlaceEx D) (j : ℕ)
    (hj : InR D j) (hIo : IotaEx Q j hj) (σ : Q.c.F →+* ℂ) (hσ : GoodEmb Q.c σ) (χ : (AE D)ˣ →* Circle) : Prop where
  modelEx : ModelEx hN Q hpq j hj σ hσ (relabType_of Q.c σ hσ (Q.Dw j))
  frameEx : FrameEx modelEx
  cover : CoverU (unfJ frameEx)
  fibre : FibreU (unfJ frameEx)

  holFD : HolomorphicSectionsFinDim (unfJ frameEx)
  genus : GenusEx (unfJ frameEx) (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) (iotaJ hIo) (letE (Q.Dw j))
    (famJ hN Q hpq j σ hσ (relabType_of Q.c σ hσ (Q.Dw j))) id (modelsJ modelEx).φ (thJ hI (modelsJ modelEx).X) (x0J modelEx)

  dictU : DictIsUnif (D.sp.W j) (dictOf genus) (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1))
    (thJ hI (modelsJ modelEx).X) (D.sp.W_rank j hj.1 hj.2)

  unitFr : ∀ g τ i, ‖dmin ((unfJ frameEx).X (dictOf genus g).1).Gm (dictOf genus g).2 τ i‖ = 1
  adelCont : AdelCont (D.sp.W j) (dictOf genus) (muOf (D.sp.W j) χ)

  latZ : σ = Q.c.F.val.toRingHom → FJ.LatZ (unfJ frameEx).X (WeightFamilies.rho D j)
  cuNe : σ = Q.c.F.val.toRingHom → FJ.CuNeF (unfJ frameEx).X (WeightFamilies.rho D j)
  expo : σ = Q.c.F.val.toRingHom → FJ.ExpoMatch (unfJ frameEx).X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

end Rows

section Collected

variable {D : D7}

def pkgJ {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {hI : InfPlaceEx D} {j : ℕ}
    {hj : InR D j} {hIo : IotaEx Q j hj} {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {χ : (AE D)ˣ →* Circle}
    (P : PkgRows hN Q hpq hI j hj hIo σ hσ χ) : PkgT Q j σ :=
  ⟨unfJ P.frameEx, dictOf P.genus, muOf (D.sp.W j) χ⟩

structure PkgOK2 (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (p : PkgT Q j σ) : Prop where
  unf : IsUnf p.1
  unTest : ∀ k x, FromTest (K := Q.c.F) (fun S _ _ => FrPt (Q.Xo j) Q.c S) (fun φ y z => FrMap φ y z) (p.1.un k x)
  chi1 : ∀ k la γ, (p.1.X k).χ la γ = 1
  dictU : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) p.2.1 (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) th hr
  xiAbs : ∀ k (τ : D.host.E →+* ℂ), ‖τ (p.1.X k).ξ0‖ = xiR D
  muUnit : MuUnit (D.sp.W j) p.2.1 p.2.2
  muCont : Continuous p.2.2
  holFD : HolomorphicSectionsFinDim p.1
  adelAut : AdelAut (D.sp.W j) p.2.1 p.2.2
  latZ : σ = Q.c.F.val.toRingHom → FJ.LatZ p.1.X (WeightFamilies.rho D j)
  cuNe : σ = Q.c.F.val.toRingHom → FJ.CuNeF p.1.X (WeightFamilies.rho D j)
  expo : σ = Q.c.F.val.toRingHom → FJ.ExpoMatch p.1.X 1 (WeightFamilies.rho D j) (D.host.g 0 * D.host.g 1)

theorem pkgJ_ok {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {hI : InfPlaceEx D} {j : ℕ}
    {hj : InR D j} {hIo : IotaEx Q j hj} {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {χ : (AE D)ˣ →* Circle}
    (P : PkgRows hN Q hpq hI j hj hIo σ hσ χ) (hA : AllTest (Q.Xo j) Q.c) (hX : XiConst D)
    (hWt : WtC (Q.Xo j) Q.c σ) (hmu : MuUnit (D.sp.W j) (dictOf P.genus) (muOf (D.sp.W j) χ) ∧ Continuous (muOf (D.sp.W j) χ)) :
    PkgOK2 Q j σ (pkgJ P) where
  unf := isUnf_unfOf _ _ _ _ P.frameEx.choose_spec.1 P.modelEx.choose_spec.1 P.cover P.fibre
    (readSecU_of _ _ _ _ P.frameEx.choose_spec P.modelEx.choose_spec.1 hWt)
  unTest := unTest_of hA _
  chi1 := P.modelEx.choose_spec.1.chi
  dictU := ⟨_, _, fun _ τ => ((hI : ∀ τ : D.host.E →+* ℂ, ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ,
    Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) τ.1).choose_spec, P.dictU⟩
  xiAbs := fun k τ =>
    (congrArg (fun z => ‖τ z‖) (P.modelEx.choose_spec.2 k).2).trans (by rw [map_neg, norm_neg]; exact hX τ)
  muUnit := hmu.1
  muCont := hmu.2
  holFD := P.holFD
  adelAut := adelAut_of P.modelEx.choose_spec.1.chi P.dictU hmu.1 P.adelCont
  latZ := P.latZ
  cuNe := P.cuNe
  expo := P.expo

end Collected

section J

variable {D : D7}

structure PkgOKJ (Q : Par D) (j : ℕ) (σ : Q.c.F →+* ℂ) (χ : (AE D)ˣ →* Circle)
    (ι₀ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E)) (p : PkgT Q j σ)
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) : Prop where
  ok : PkgOK2 Q j σ p
  muVal : MuVal (D.sp.W j) χ p.2.2
  modelW : ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr (p.1.X k)
  familyUniformisationBasePointOrthogonal : ∀ k, IsOrthogonalFrame (p.1.X k) x₀
  adPin : ∃ (hr : (D.sp.W j).rank = D.R.r) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin ((Q.Dw j).mult τ))
    (F : FamilyUnif (Q.Xo j) (σ.comp (IntermediateField.inclusion Q.c.le).toRingHom) (fun i => relab Q.c σ (e i).1))
    (ik : p.1.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (p.1.X k).Λ)
    (th : ∀ k, (p.1.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀
    LatEmb (D.sp.W j) ι ∧ LatIsom (D.sp.W j) (Q.Dw j).EF ι ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictLat p.1 (D.sp.W j) hr p.2.1 ι e F ik φ th x₀

theorem pkgJ_okJ {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q} {hI : InfPlaceEx D} {j : ℕ}
    {hj : InR D j} {hIo : IotaEx Q j hj} {σ : Q.c.F →+* ℂ} {hσ : GoodEmb Q.c σ} {χ : (AE D)ˣ →* Circle}
    (P : PkgRows hN Q hpq hI j hj hIo σ hσ χ) (hA : AllTest (Q.Xo j) Q.c) (hX : XiConst D)
    (hWt : WtC (Q.Xo j) Q.c σ) (R : MuRows (D.sp.W j) χ) :
    PkgOKJ Q j σ χ hIo.choose (pkgJ P) (x0J P.modelEx) where
  ok := pkgJ_ok P hA hX hWt (muOK_of R P.unitFr)
  muVal := muVal_muOf R.detRoot R.chiWD
  modelW := ⟨_, P.modelEx.choose_spec.2⟩
  familyUniformisationBasePointOrthogonal := fun k => by
    have hB := P.modelEx.choose_spec.1
    have hW := P.modelEx.choose_spec.2
    refine base_frame_orthonormal_of_eq (Finset.ext fun τ => ((hB.type _).2 τ).trans ((hB.type k).2 τ).symm)
      ((hW _).1.trans (hW k).1.symm) ((hB.type _).1.trans (hB.type k).1.symm)
  adPin := ⟨D.sp.W_rank j hj.1 hj.2, _, letE (Q.Dw j), famJ hN Q hpq j σ hσ (relabType_of Q.c σ hσ (Q.Dw j)), id, (modelsJ P.modelEx).φ,
    thJ hI (modelsJ P.modelEx).X, hIo.choose_spec.1, hIo.choose_spec.2,
    fun _ τ => ((hI : ∀ τ : D.host.E →+* ℂ, ∃ θ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ,
      Formalism.MainNotions.StandardLattice.IsInfEmb τ θ) τ.1).choose_spec,
    dictLat_unfOf _ _ _ _ P.frameEx.choose_spec.1 P.modelEx.choose_spec.1 P.genus⟩

structure LawsJRest (hN : N1c) (Q : Par D) (hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q)
    (chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle) : Prop extends BaseRows Q where
  pkg : ∀ j (hj : InR D j) σ (hσ : GoodEmb Q.c σ), PkgRows hN Q hpq (infPlaceEx_holds D) j hj (iota j hj) σ hσ (chiW j σ)
  muRows : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuRows (D.sp.W j) (chiW j σ)

  muConj : ∀ j, InR D j → ∀ σ, GoodEmb Q.c σ → MuConj Q.c.F.val.toRingHom σ (chiW j Q.c.F.val.toRingHom) (chiW j σ)

  intAll : ∀ j, InR D j → IntAll (Q.Xo j) Q.c

  kfHalf : ∀ j, InR D j → KfHalf (D.sp.W j) (kfW (D.sp.W j) (D.host.g 0 * D.host.g 1)) Q.l.M
    (Q.l.Mb.map (Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E))

variable {hN : N1c} {Q : Par D} {hpq : ∀ j, 1 ≤ (Q.Dw j).p + (Q.Dw j).q}
  {chiW : ℕ → (Q.c.F →+* ℂ) → (AE D)ˣ →* Circle}

open Classical in

def iotaOf (L : LawsJRest hN Q hpq chiW) (j : ℕ) : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E) :=
  if hj : InR D j then (L.iota j hj).choose else 0

theorem pkgExJ (L : LawsJRest hN Q hpq chiW) (j : ℕ) (σ : Q.c.F →+* ℂ) :
    ∃ q : PkgT Q j σ × ((D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ),
      ∀ hj : InR D j, GoodEmb Q.c σ → PkgOKJ Q j σ (chiW j σ) (L.iota j hj).choose q.1 q.2 := by
  by_cases hj : InR D j
  · by_cases hσ : GoodEmb Q.c σ
    · exact ⟨(pkgJ (L.pkg j hj σ hσ), x0J (L.pkg j hj σ hσ).modelEx), fun _ _ =>
        pkgJ_okJ (L.pkg j hj σ hσ) (L.allTest j hj) (xiConst_holds D) (L.wtC j hj σ hσ) (L.muRows j hj σ hσ)⟩
    · exact ⟨(Classical.choice (L.dataAll j σ), fun _ => 1), fun _ h => absurd h hσ⟩
  · exact ⟨(Classical.choice (L.dataAll j σ), fun _ => 1), fun h => absurd h hj⟩

def pkgOfJ (L : LawsJRest hN Q hpq chiW) (j : ℕ) (σ : Q.c.F →+* ℂ) :
    PkgT Q j σ × ((D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ) :=
  (pkgExJ L j σ).choose

def coreJOf (L : LawsJRest hN Q hpq chiW) : CoreJ D where
  toCore := coreOfP Q (fun j σ => (pkgOfJ L j σ).1) L.half.choose
  cE _ _ _ := 1
  chiW := chiW
  x₀ j σ := (pkgOfJ L j σ).2
  iota := iotaOf L

end J

section At

variable (D : D7) (hF : OFull D) (hz : OZeta D) (hN : N1ab) (l : Level (hostOfRecord D))
  (hl : l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1)

end At

end Formalism.L2.Pj.V3
