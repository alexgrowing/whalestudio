import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegPreOfPolAV
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsGenThetaOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsSharpAndPrim
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.EighthPowerFactor

open CechPic

theorem relAmple_diag_lam {k : Type} [Field k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen)
    (ha : Out.RelAmple B M) : Out.RelAmple B ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) := by
  have hN : ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left).IsLB := pull_isLB (LB.isLB_linComb hM _ _) _
  have hι : (M.pull ((𝟙 B)⁻¹ : B ⟶ B).left).IsLB := pull_isLB hM _
  have hD1 : (LB.div ((abelian₂ B M).pull (lift (𝟙 B) (𝟙 B)).left) M).IsLB := LB.isLB_div hN hM
  have hD := LB.isLB_div hD1 hι
  haveI : IsProper B.hom := IsAbelianScheme.proper
  have hI : ((𝟙 B)⁻¹ : B ⟶ B) ≫ (𝟙 B)⁻¹ = 𝟙 B := by
    first
    | rw [GrpObj.comp_inv, Category.comp_id, inv_inv]
    | rw [GrpObj.inv_def, Category.id_comp, GrpObj.inv_inv]
    | simp [GrpObj.comp_inv]
  haveI : IsIso ((𝟙 B)⁻¹ : B ⟶ B) := ⟨⟨_, hI, hI⟩⟩
  haveI : IsIso ((𝟙 B)⁻¹ : B ⟶ B).left :=
    ⟨⟨((𝟙 B)⁻¹ : B ⟶ B).left, by rw [← Over.comp_left, hI, Over.id_left],
      by rw [← Over.comp_left, hI, Over.id_left]⟩⟩
  have h0 : ∀ (L : LB (Sp k)), L.IsLB → ∃ t : LB.Gen L, t.IsGen := by
    intro L hL
    have hcov : ∀ y : Sp k, ∃ i, y ∈ L.U i := fun y => by
      have hy : y ∈ (⨆ i, L.U i) := by rw [hL.1]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using hy
    have hs : ∀ y y' : Sp k, y = y' := fun y y' => Subsingleton.elim (α := PrimeSpectrum k) y y'
    obtain ⟨y₀⟩ : Nonempty (PrimeSpectrum k) := inferInstance
    obtain ⟨i₀, hi₀⟩ := hcov y₀
    exact GlobalTheory.DescendedPrincipal.exists_gen_of_chart hL i₀ fun y => by rw [← hs y₀ y]; exact hi₀
  set c := GlobalTheory.CechPic.cls M hM
  have e1 : (1 : B ⟶ B).left = (toUnit B).left ≫ η[B].left := rfl
  have h1 : GlobalTheory.CechPic.pull (1 : B ⟶ B).left c = 0 := by
    rw [e1, GlobalTheory.CechPic.pull_comp]
    obtain ⟨L, hL, hLc⟩ := GlobalTheory.CechPic.cls_surj (GlobalTheory.CechPic.pull η[B].left c)
    rw [← hLc, (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 (h0 L hL), map_zero]
  have e5 : GlobalTheory.CechPic.lam c (𝟙 B)⁻¹ (𝟙 B) = -GlobalTheory.CechPic.pull ((𝟙 B)⁻¹ : B ⟶ B).left c - c := by
    unfold GlobalTheory.CechPic.lam
    rw [inv_mul_cancel, Over.id_left, GlobalTheory.CechPic.pull_id, h1]
    abel
  have e3 := GlobalTheory.CechPic.lam_mul_left hM hΘ (𝟙 B) (𝟙 B)⁻¹ (𝟙 B)
  rw [mul_inv_cancel, GlobalTheory.CechPic.lam_one_left, e5] at e3
  have e2 : GlobalTheory.CechPic.cls (abelian₂ B M) (LB.isLB_linComb hM _ _) = GlobalTheory.CechPic.lam c (fst B B) (snd B B) :=
    GlobalTheory.CechPic.cls_cube_two hM _ _ _
  have hc : GlobalTheory.CechPic.cls _ hD = 0 := by
    rw [GlobalTheory.CechPic.cls_div hD1 hι hD, GlobalTheory.CechPic.cls_div hN hM hD1,
      GlobalTheory.CechPic.cls_pull (L := abelian₂ B M) (LB.isLB_linComb hM _ _) _ hN, GlobalTheory.CechPic.cls_pull hM _ hι, e2,
      GlobalTheory.CechPic.pull_lam, lift_fst, lift_snd]
    rw [eq_comm, ← sub_eq_zero] at e3
    rw [← e3]
    abel
  have H := (GlobalTheory.CechPic.cls_eq_zero_iff hD).1 hc
  have hMa := (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hM).1 ha
  exact (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine B hN).2 (hMa.tensor (hMa.pull_of_isFinite _) hN H)

theorem weilIs_one_one (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    {M : LB A.left} (hM : M.IsLB) (T : Over S) : Out.WeilIs A M 1 (1 : T ⟶ A) 1 1 := by
  refine GlobalTheory.DescendedPrincipal.weilIs_one_right hG hA hM fun _ => ⟨⊤, trivial, ?_⟩
  exact match GlobalTheory.DescendedPrincipal.exists_theta_one (A := A) hM _ with
  | ⟨θ, hθ, _⟩ => ⟨θ, hθ.trans (MonObj.comp_one _).symm⟩

open SiegelOfPolarised PrimNorm in

def siegOne (hG : Out.GlobalFnsSt) {k : Type} [Field k] {B : Over (Sp k)} [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) {M : LB B.left} (hM : M.IsLB) (g : ℕ) :
    SiegPre g 1 ((1 : kˣ) : k) (𝟙 (Sp k)) where
  A := B
  ab := hB
  P := abelian₂ B M
  isLB := LB.isLB_linComb hM _ _
  rig₁ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  rig₂ := hasGen_lam_pull hM _ _ (by simp [diff₂])
  symm := lbIso_lam_pull hM _ _ (diff₂_comm _ _)
  lev := fun _ => 1
  lev_add := fun _ _ => (_root_.mul_one _).symm
  lev_tors := fun _ => one_pow _
  geom := by
    intro K _ _ x β z _ hz
    obtain rfl : z = 1 := Units.ext (by simpa using hz)
    refine ⟨fun a => ⟨fun _ => ⟨a, (one_smul _ _).symm⟩, fun _ => MonObj.comp_one _⟩,
      fun y hy => ⟨0, (MonObj.comp_one _).trans ((pow_one y).symm.trans hy).symm⟩, fun a b => ?_⟩
    rw [MonObj.comp_one, one_zpow, show unitOn (1 : Kˣ) = 1 from map_one _]
    exact weilIs_one_one hG hB (pull_isLB (LB.isLB_linComb hM _ _) _) _

theorem exists_matrices {W : Matrix (Fin 8) (Fin 8) ℤ} (hW : (W + W.transpose).det = 1) :
    ∃ (a : (Fin 8 × Fin 8) ⊕ Bool → Matrix (Fin 8) (Fin 8) ℤ) (w w' : (Fin 8 × Fin 8) ⊕ Bool),
      (W + W.transpose) * a w = W ∧ (W + W.transpose) * a w' = W.transpose ∧
        ∀ u v, ∃ j, a j = Matrix.single u v 1 := by
  have hu : IsUnit (W + W.transpose).det := by rw [hW]; exact isUnit_one
  refine ⟨fun j => Sum.elim (fun p => Matrix.single p.1 p.2 1)
      (fun b => if b then (W + W.transpose)⁻¹ * W else (W + W.transpose)⁻¹ * W.transpose) j,
    Sum.inr true, Sum.inr false, ?_, ?_, fun u v => ⟨Sum.inl (u, v), rfl⟩⟩
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]
  · simp [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu]

theorem isMonHom_of_coord {S : Scheme.{0}} {A G X : Over S} [GrpObj A] [GrpObj G] [GrpObj X] {n : ℕ}
    {pr : Fin n → (G ⟶ A)} (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) {f : X ⟶ G}
    (hf : ∀ u, IsMonHom (f ≫ pr u)) : IsMonHom f := by
  have ext : ∀ {T : Over S} (x x' : T ⟶ G), (∀ u, x ≫ pr u = x' ≫ pr u) → x = x' := fun x x' h =>
    (hu _ (fun u => x' ≫ pr u)).unique h (fun _ => rfl)
  constructor
  · refine ext _ _ fun u => ?_
    rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine ext _ _ fun u => ?_
    rw [Category.assoc, Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom, ← Category.assoc,
      ← tensorHom_comp_tensorHom]

theorem exists_polAV_hypS_retract : ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ M : LB B.left, M.IsLB → Out.RelAmple B M → Out.KTriv B M → ∃ (Q : Out.PolAV (Sp k)) (i : B ⟶ Q.A) (r : Q.A ⟶ B), (letI := Q.isAb.comm; GlobalTheory.ZH.HypS Q.A Q.L) ∧ IsMonHom i ∧ IsMonHom r ∧ i ≫ r = 𝟙 B := by
  intro k _ _ B _ g hB hd M hM ha hK
  obtain ⟨hL1, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  have hG : Out.GlobalFnsSt := hL1.globalFns
  letI : IsCommMonObj B := hB.comm
  have hΘ : ∃ t : LB.Gen (Theta B M), t.IsGen := GlobalTheory.exists_gen_theta_of_isAbelianScheme k B hB M hM
  let b : GlobalTheory.ZM.TBase k 1 := ⟨1, by simp, fun K _ β => by simp [IsPrimitiveRoot.one]⟩
  let c := siegOne hG hB hM g
  have hc : c.Principal :=
    ⟨relAmple_diag_lam hB hM hΘ ha, fun T x hx => GlobalTheory.SiegelOfPolarised.eq_one_of_lam hM hK x hx⟩
  obtain ⟨W, hW, hbas⟩ := GlobalTheory.ZM.exists_isE8_isSharpBasis
  obtain ⟨bas, hb⟩ := hbas g
  obtain ⟨a, w, w', hw, hw', hs⟩ := exists_matrices hW.2
  obtain ⟨t, hsh, hp⟩ := GlobalTheory.exists_isSharp_and_prim hL1 hL2 GlobalTheory.Moduli.cube_of_isLB g (8 * g) W _ a w w' bas
    hW hb hw hw' hs 1 k b (Sp k) (𝟙 _) c (show (1 : kˣ) ^ 1 = 1 from one_pow 1) odd_one hc hd
  obtain ⟨pr, hpr, hu, -, -, -⟩ := hsh
  obtain ⟨i, hi, -⟩ := hu B (fun _ => 𝟙 B)
  letI := t.ab.comm
  refine ⟨t.pol, i, pr 0, ⟨t.act w, t.act w', t.hom w, t.hom w', hp.1, hp.2.2, hp.2.1⟩, ?_, hpr 0, hi 0⟩
  exact isMonHom_of_coord hpr hu (fun u => by rw [hi u]; exact (inferInstance : IsMonHom (𝟙 B)))

end GlobalTheory.EighthPowerFactor

end
