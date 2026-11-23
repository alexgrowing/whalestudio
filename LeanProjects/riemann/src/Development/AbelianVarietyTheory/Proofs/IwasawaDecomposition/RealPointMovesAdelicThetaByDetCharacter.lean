import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateModelSameThetaFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumRealPlacesFockVacuumCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIdeleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetBlockConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulFunEqOneOfEqOneOnMaxCompact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsFundamentalDomainOfHaar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.RealMove

open GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant (detPos detNeg vacChar)
open scoped ComplexOrder

variable {D : D7} {S T : HSp D}

theorem root_eq {χ : (AE D)ˣ →* Circle} {n : ℕ} (h : ResEta D χ n) (hn : Even n) {g : GA D T} {x x' : (AE D)ˣ}
    (hx : IsDetRoot T g x) (hx' : IsDetRoot T g x') : χ x' = χ x := by
  obtain ⟨a, rfl⟩ := (GlobalTheory.Member.isDetRoot_laws D T).2.1 g x x' hx hx'
  obtain ⟨⟨η, hη⟩, h2⟩ := h
  obtain ⟨m, rfl⟩ := hn
  rw [map_mul, h2 η hη a, pow_add, ← mul_pow, GlobalTheory.VolHeckeCompare.IsEta_mul_self hη, one_pow, mul_one]

theorem om_compact (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {s : Fam T} (hs : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {k : GA D T} (hk : k ∈ GinfC T)
    (hc : ∀ τ, s τ * compAt C.θ τ (Formalism.L2.Theta.mt T k) = compAt C.θ τ (Formalism.L2.Theta.mt T k) * s τ)
    {y : (AE D)ˣ} (hy : IsDetRoot T k y) {f : WO S T → ℂ} (hf : IsThetaFunO C.ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO C.ψ S T) C.θ τ (cplxO 1 (s τ)) f) :
    om (1, k) f = (((χS y : Circle) : ℂ) * vacChar C.θ T s S.rank (fun _ => 0) k) • f := by
  have hdet : ∀ τ, (gramAt D T τ).det ≠ 0 := fun τ => by
    have := (hs τ).2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨y₀, hy₀, hv₀⟩ := GlobalTheory.OneMapRef.RealMove.exists_root C.inf T hdet k hk
  have hS : ∀ τ, IsCartanInv (gramAt D S τ) 1 := fun τ => by
    have e : gramAt D S τ = 1 := by
      unfold gramAt
      rw [C.m.gS]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    rw [e]
    exact ⟨one_mul _, by simp, by rw [one_mul]; exact Matrix.PosDef.one⟩
  have h1 : IsDetRoot S 1 1 := by simp [IsDetRoot]
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D C.ψ hW.std S T C.θ C.inf χS χT om η hη hW (fun _ => 1) s hS hs 1 (one_mem _) k hk
    (fun τ => by rw [one_mul, mul_one]) hc 1 y₀ h1 hy₀ f hf hv, root_eq hW.resS C.even hy₀ hy]
  congr 1
  obtain ⟨m, hm⟩ := C.even
  have e1 := hv₀ (η * (η ^ (S.rank + 1))⁻¹) (fun _ => -(m : ℤ)) fun τ => by
    have := GlobalTheory.OneMapRef.RealMove.hasInfExp_twist (hη.2.2.2 τ) (hη.2.2.2 τ) (S.rank + 1)
    convert this using 1
    rw [hm]
    push_cast
    ring
  have e2 : ((χT * (η ^ T.rank)⁻¹) 1)⁻¹ * (χS * (η ^ S.rank)⁻¹) y₀ = χS y₀ * (η * (η ^ (S.rank + 1))⁻¹) y₀ := by
    simp only [map_one, inv_one, one_mul, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, pow_succ,
      mul_inv]
    rw [mul_left_comm (η y₀), mul_inv_cancel, mul_one]
  rw [e2, Circle.coe_mul, e1, mul_assoc, ← Finset.prod_mul_distrib, vacChar]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨p, -, hd⟩ := GlobalTheory.OneMapRef.RealMove.detPlus_one (n := S.rank) (s τ) (hs τ).1
  obtain ⟨d1, d2⟩ := hd (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)) (compAt C.θ τ (Formalism.L2.Theta.mt T k)) (hc τ)
  have e3 : (compAt C.θ τ (Formalism.L2.Theta.mt S 1⁻¹)).det = 1 := by
    rw [GlobalTheory.OneMapRef.RealMove.det_compAt, inv_one]
    unfold Formalism.L2.Theta.mt
    rw [map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have e4 : (compAt C.θ τ (Formalism.L2.Theta.mt T k)).det ≠ 0 := by
    intro h0
    have h2 := congrArg det (GlobalTheory.Ker.ONBasis.compAt_unitary C τ k)
    rw [det_mul, h0, mul_zero] at h2
    exact hdet τ h2.symm
  have hc' := hc τ
  rw [d1, e3]
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T k) = b at *
  have p1 : detPos (s τ) b = ((1 / 2 : ℂ) • (1 + s τ) * b + (1 / 2 : ℂ) • (1 - s τ)).det := by
    rw [detPos, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, hc', one_mul, mul_one]
  have p2 : detNeg (s τ) b = ((1 / 2 : ℂ) • (1 - s τ) * b + (1 / 2 : ℂ) • (1 + s τ)).det := by
    rw [detNeg, detPos, Matrix.mul_smul, Matrix.smul_mul, ← sub_eq_add_neg, sub_neg_eq_add, mul_sub, sub_mul, hc',
      one_mul, mul_one]
  rw [← p1, ← p2] at d2
  rw [← p1, d2]
  rw [d2] at e4
  have h0 := left_ne_zero_of_mul e4
  have e5 : S.rank / 2 = m := by omega
  rw [e5, zero_add, zero_sub, _root_.zpow_neg, _root_.zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast, hm,
    one_pow, mul_one, mul_pow, pow_add, mul_inv]
  have := pow_ne_zero m h0
  field_simp

theorem om_real (C : GlobalTheory.Ker.Ctx S T) {χS χT η : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO C.ψ S T χS χT om) (hη : IsEtaTilde D η)
    {a : GA D T} (ha : a ∈ GinfC T) {y : (AE D)ˣ} (hy : IsDetRoot T a y) {B : C.Bas} (hB : C.IsB B)
    {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ) :
    om (1, a) (C.Th (C.xB B) φ) = ((χS y : Circle) : ℂ) • C.Th (C.xB (C.mvB a B)) φ := by
  obtain ⟨χ, -, χmul, hχ⟩ := GlobalTheory.FrameEquiv.exists_real_character D S T C om (GlobalTheory.Ker.isWeak_of_datum hW)
  have hJ := (GlobalTheory.Ker.onBasis_frame_period D S T C).2
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  by_cases h0 : φ = 0
  · rw [hχ a ha B hB φ hφ, h0, GlobalTheory.FrameEquiv.RealChar.Th_zero C
      (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 a).1), smul_zero, smul_zero]
  obtain ⟨hex, -, -, hmul⟩ := GlobalTheory.Member.isDetRoot_laws D T
  choose rt hrt using hex
  have hne : ∀ g, ((χS (rt g) : Circle) : ℂ) ≠ 0 := fun g => Circle.coe_ne_zero _
  have key := GlobalTheory.FrameEquiv.mulFun_eq_one_of_eq_one_on_maxCompact D T C.θ C.inf (C.sB B)
    (fun τ => ((hJ B hB).2.2.1 τ).1) (fun u => χ u / (χS (rt u) : Circle))
    (fun u hu u' hu' => by
      simp only [χmul u hu u' hu']
      rw [root_eq hW.resS C.even (hmul _ _ _ _ (hrt u) (hrt u')) (hrt (u * u')), map_mul, Circle.coe_mul,
        mul_div_mul_comm])
    (fun k hk hc => by
      have e1 := om_compact C hW hη (fun τ => ((hJ B hB).2.2.1 τ).1) hk (fun τ => (hc τ).symm) (hrt k)
        (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).1.1 ((GlobalTheory.Ker.fvec_Th_zero D S T C).2 B hB φ hφ).1
      have e2 := hχ k hk B hB φ hφ
      have e3 := GlobalTheory.FrameEquiv.CompactMove.Th_mvB D S T C B hB k hk hc φ hφ
      rw [← smul_smul, ← e3, e2] at e1
      have e4 := smul_left_injective ℂ (GlobalTheory.FrameEquiv.RealChar.Th_ne_zero C
        (GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C ((hJ B hB).2.2.2.2.2 k).1) hφ h0) e1
      show χ k / (χS (rt k) : Circle) = 1
      rw [e4, div_self (hne k)]) a ha
  rw [hχ a ha B hB φ hφ, (div_eq_one_iff_eq (hne a)).1 key, root_eq hW.resS C.even hy (hrt a)]

set_option maxHeartbeats 1000000 in

theorem zak_om_real : ∀ (D : D7) (S T : HSp D) (r g : ℕ) (hr : T.rank = r) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (X : Data D.host.E r) (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hS : IsSet ψ θ S T hr X eT bas), ∀ (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → (∃ η, IsEtaTilde D η) → ∀ Z : Fam T, IsONeg T X.p0 Z → ∀ a ∈ GinfC T, ∀ y : (AE D)ˣ, IsDetRoot T a y → ∀ φ : TF S.rank g, GlobalTheory.SW.IsSB φ → ∀ f, Zak ψ θ hr eT bas idx (frOf hr eT Z) φ f → Zak ψ θ hr eT bas idx (frOf hr eT (mvZ θ a Z)) (((χS y : Circle) : ℂ) • φ) (om (1, a) f) := by
  intro D S T r g hr ψ θ X eT bas idx hS χS χT om hW ⟨η, hη⟩ Z hZ a ha y hy φ hφ f hf
  obtain ⟨X', m, hq', bas', idx', hs, π, -, -, -, H⟩ := GlobalTheory.T.exists_conjugateModel_same_thetaFunctions D S T r g hr ψ θ X eT bas idx hS (r - X.p0)
    (Nat.add_sub_cancel' X.p0_le)
  set C := ctxOf hS.1 hS.2.1 hS.2.2.2.1 X' m hq' bas' idx' hs with hC
  have hB := (H Z).1.1 hZ
  have em : (fun ρ => (mvZ θ a Z ρ).submatrix id π) = C.mvB a fun ρ => (Z ρ).submatrix id π := by
    funext ρ
    ext i j
    rfl
  have hB' := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 _ hB).2.2.2.2.2 a).1
  have hZ' : IsONeg T X.p0 (mvZ θ a Z) := (H _).1.2 (em ▸ hB')
  have hd := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB
  have hd' := GlobalTheory.FrameEquiv.RealChar.xB_mem_dom C hB'
  have e1 := (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd φ hφ).2 f ((((H Z).2 hZ).2.1 φ f).2 hf)
  refine (((H _).2 hZ').2.1 _ _).1 ?_
  have hφ' : GlobalTheory.SW.IsSB (((χS y : Circle) : ℂ) • φ) := (isSB_algebra_haar_linear _ _ _ _ _ hφ hφ).2.1 _
  rw [em, e1, om_real C hW hη ha hy hB hφ, ← (GlobalTheory.Ker.Ctx.th_laws D S T C _ hd' φ hφ).2.1]
  exact (GlobalTheory.Ker.ZakEx.isZak_Th D S T C _ hd' _ hφ').1

end GlobalTheory.OneMapRef.RealMove
