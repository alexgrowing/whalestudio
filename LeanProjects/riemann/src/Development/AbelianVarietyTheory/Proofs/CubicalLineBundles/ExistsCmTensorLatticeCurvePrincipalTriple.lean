import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueCmHermitianLatticeFormStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorBundle
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorPairingIdentityOfPureTensors
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfPerfect
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleLineBundleOfPositiveHermitianCmFormStatement
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimensionStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

theorem exists_isTen : Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsNoetherianRing R] (ω : R) (C : Ell H R ω) (D : Datum H) (ε : ℤˣ) (h : D.La → D.La → OK H), IsKForm D ε h → (∀ x : D.La, x ≠ 0 → 0 < (ε : ℤ) * D.EF (H.w0 • x) x) → ∃ T : PAT H (Sp R), Nonempty (IsTen C D h T) ∧ T.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  intro laws E _ _ _ H R _ _ ω C D ε h hK hpos
  obtain ⟨h₀, -, huniq, hbar, hE, -, -, n, x, y, hxy⟩ := GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H D ε
  obtain rfl := huniq h hK
  obtain ⟨-, -, ⟨br, hbr, hw, hbb⟩, -, -, hM⟩ := OK_isDedekindDomain_and_projective E H
  obtain ⟨hfin, hproj, -⟩ := hM D.La D.fin D.proj
  let t := Serre.isTensor D.La C.act
  obtain ⟨c, τ, hc⟩ : ∃ (c : OAct (𝓞 E) (Serre.tensorObj D.La C.act))
      (τ : Serre.IsTensor _ (Serre.comapAct c (algebraMap (OK H) (𝓞 E))) C.P.A C.act D.La),
      ∀ (s : 𝓞 E) a, τ.tmul (s • a) = τ.tmul a ≫ c.act s := by
    have key : ∀ b', b' = Serre.tensorAct D.La C.act → ∃ τ : Serre.IsTensor _ b' C.P.A C.act D.La,
        ∀ a, τ.tmul a = t.tmul a := by
      rintro _ rfl
      exact ⟨t, fun _ => rfl⟩
    obtain ⟨τ, hτ⟩ := key _ (t.comapAct_algAct (𝓞 E))
    exact ⟨t.algAct (𝓞 E), τ, fun s a => by rw [hτ, hτ, t.tmul_algAct]⟩
  have hA : IsAbelianScheme (Serre.tensorObj D.La C.act) := τ.isAbelianScheme C.P.isAb
  obtain ⟨rig, hrig⟩ := C.P.rigid
  obtain ⟨cubP⟩ := (laws.cube _ C.P ⟨C.P.L, rig, C.P.isLB, hrig⟩ rfl).1
  have hθP : ∃ t : LB.Gen (Theta C.P.A C.P.L), t.IsGen := ⟨cubP.t, cubP.isGen⟩
  obtain ⟨N, hN, -, hθ, hp⟩ := GlobalTheory.TensorBundle.exists_tensor_bundle _ (OK H) C.P.A _ C.act _ D.La τ br (wK H) C.P.L h₀
    hfin hproj hw hbb (fun a b => Subtype.ext ((hbar a b).trans (hbr _).symm)) C.P.isLB hθP
    (fun a => C.adj a (br a) (hbr a))
  obtain ⟨PP, cub, sym, -, hΛ, prim, adj⟩ := GlobalTheory.PrimNorm.exists_primitive_normalisation laws.globalFns E H _ _ c N
    hA hN hθ fun s => by
      have := GlobalTheory.LamCalc.lamEq_of_tmul _ (OK H) C.P.A _ C.act _ D.La τ _ _ D.La τ _ _ N N (c.act s) (𝟙 _) (𝟙 _)
        (c.act (H.bar s)) hN hN hθ hθ (c.hom _) inferInstance inferInstance (c.hom _) fun m m' => by
          rw [← hc, ← hc, Category.comp_id, Category.comp_id]
          have a := hp (s • m) m'
          rw [hE] at a
          exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ hN _ _)
            a (hp m (H.bar s • m')).symm
      simpa only [LamEq, Category.comp_id] using this
  have hp' : ∀ m m', LamEq PP.L (τ.tmul m) (τ.tmul m') C.P.L (C.act.act (h₀ m m')) (𝟙 C.P.A) := fun m m' =>
    LBIso.trans (DVR.linComb_isLB _ PP.isLB _ _) (DVR.linComb_isLB _ hN _ _) (DVR.linComb_isLB _ C.P.isLB _ _)
      (hΛ.chartPull
        (GlobalTheory.PrimNorm.chartSquare PP.L (lift (fst C.P.A C.P.A ≫ τ.tmul m) (snd C.P.A C.P.A ≫ τ.tmul m'))
          (lift_fst _ _).symm (lift_snd _ _).symm)
        (GlobalTheory.PrimNorm.chartSquare N (lift (fst C.P.A C.P.A ≫ τ.tmul m) (snd C.P.A C.P.A ≫ τ.tmul m'))
          (lift_fst _ _).symm (lift_snd _ _).symm))
      (hp m m')
  have hθ' : ∃ t : LB.Gen (Theta _ PP.L), t.IsGen := ⟨cub.t, cub.isGen⟩
  let s : SAB H (Sp R) :=
    { G := Serre.tensorObj D.La C.act, semi := GlobalTheory.isSemiAbelian_of_isAbelianScheme _ hA, act := c, PP := PP,
      cub := cub, sym := sym, adj := adj, prim := prim }
  exact ⟨⟨s, hA, _, GlobalTheory.T.cmTensor_smoothOfRelativeDimension E H R ω C D _ _ ⟨τ⟩, ObjDim.sym,
    GlobalTheory.T.relAmple_lineBundle_of_positive_hermitian_cm_form laws E H R ω C D ε _ _ _ τ PP.L hK hpos PP.isLB hθ' prim hp',
    GlobalTheory.PerfectTensorKernel.kTriv_of_perfect _ (OK H) C.P.A _ C.act _ D.La τ C.P.L PP.L h₀ n x y hxy C.P.isLB PP.isLB
      hθP hθ' hp' C.P.ktriv⟩, ⟨⟨τ, hc, hp'⟩⟩, rfl⟩

end GlobalTheory.CM
end
