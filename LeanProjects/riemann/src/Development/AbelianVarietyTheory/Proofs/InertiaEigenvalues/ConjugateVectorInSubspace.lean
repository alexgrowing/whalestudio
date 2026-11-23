import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotInDetectByEqvMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteTypeVectorDetectedLocalComponentEquivarianStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTrivOutsideLoc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionGLSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivOutsideMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowsAtLevelsFixedPrincipalCongruenceTypePlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorEqGoodIdempotentTypePlacesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitCompletionSymmContinuous
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeVec

theorem pi_ind {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type} [∀ i, Group (M i)] (P : (∀ i, M i) → Prop) (h1 : P 1)
    (hm : ∀ g i (m : M i), P g → P (Pi.mulSingle i m * g)) : ∀ g, P g := by
  intro g
  have key : ∀ t : Finset ι, P (fun i => if i ∈ t then g i else 1) := by
    intro t
    induction t using Finset.induction_on with
    | empty => convert h1 using 1; funext i; simp
    | insert a t ha ih =>
      have e : (fun i => if i ∈ insert a t then g i else 1) =
          Pi.mulSingle a (g a) * (fun i => if i ∈ t then g i else 1) := by
        funext i
        by_cases hi : i = a
        · subst hi; simp [ha]
        · simp [Finset.mem_insert, hi, Pi.mulSingle_apply]
      rw [e]; exact hm _ _ _ ih
  simpa using key Finset.univ

def conjL {X : Type} : (X → ℂ) →ₛₗ[starRingEnd ℂ] (X → ℂ) where
  toFun f := fun g => star (f g)
  map_add' f f' := by funext g; simp
  map_smul' c f := by funext g; simp [mul_comm]

theorem loc_piece {L : Type} [Field L] [NumberField L] [IsCMField L] {n g : ℕ} [Fact g.Prime] (π : NG.FinTyp L n)
    (s : SplitPlace L) {w : HeightOneSpectrum (𝓞 L)} (h : s.w = w)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion L))) (hτ : GlobalTheory.HeightCounting.IsLocS π.S s (h ▸ τ))
    (ii : ℚ_[g] ≃+* w.adicCompletion L) (hii : Continuous ii) :
    ∃ j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L), Continuous j ∧
      ∀ f ∈ π.S, f ≠ 0 → ∃ p : (GAf L n → ℂ) →ₗ[ℂ] τ.V, p f ≠ 0 ∧
        ∀ (y : GL (Fin n) ℤ_[g]) (x : GAf L n), IsLiftAt s j y x → ∀ f' ∈ π.S,
          p (NG.rt L n x f') = τ.ρ (Matrix.GeneralLinearGroup.map ii.toRingHom (GlobalTheory.GLp.inc g n y)) (p f') := by
  subst h
  obtain ⟨i, Tm, hic, hi1, hinj, hmem, heq⟩ := hτ
  refine ⟨ii.trans i.symm, (GlobalTheory.splitCompletion_symm_continuous L s i hic hi1).comp hii, fun f hf hf0 => ?_⟩
  obtain ⟨p, hp0, hpe⟩ := GlobalTheory.T.finiteType_vector_detected_localComponent_equivariant L n π s τ i Tm hic hi1 hinj hmem heq f hf hf0
  refine ⟨p, hp0, fun y x hx f' hf' => ?_⟩
  have e : ∀ Z : GL (Fin n) ℚ_[g], Matrix.GeneralLinearGroup.map i.toRingHom
      (Matrix.GeneralLinearGroup.map (ii.trans i.symm).toRingHom Z) = Matrix.GeneralLinearGroup.map ii.toRingHom Z := by
    intro Z; ext a b; simp
  rw [hpe x hx.1 f' hf', hx.2, e]

theorem isotIn_stable {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) (π : NG.FinTyp D.host.E n) (h : GAf D.host.E n) :
    ∀ z ∈ principalLevelFrame.isotIn ρ C π, ρ h z ∈ principalLevelFrame.isotIn ρ C π := by
  intro z hz
  have key : principalLevelFrame.isotIn ρ C π ≤ (principalLevelFrame.isotIn ρ C π).comap (ρ h) := by
    refine iSup₂_le fun Φ hΦ => ?_
    rintro _ ⟨f, rfl⟩
    rw [Submodule.mem_comap, ← hΦ.1 h f]
    exact (le_iSup₂ (f := fun (Φ : π.S →ₗ[ℂ] A) (_ : principalLevelFrame.IsEqvA ρ π Φ ∧ LinearMap.range Φ ≤ C) => LinearMap.range Φ) Φ hΦ)
      ⟨_, rfl⟩
  exact key hz

theorem detect_conj {D : D7} {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (ρ : GAf D.host.E n →* Module.End ℂ A)
    (C : Submodule ℂ A) (π : NG.FinTyp D.host.E n) (c : GAf D.host.E n) (y : A) (hy : y ∈ principalLevelFrame.isotIn ρ C π) (hy0 : y ≠ 0) :
    ∃ q : A →ₗ[ℂ] (GAf D.host.E n → ℂ), q y ≠ 0 ∧ ∀ z ∈ principalLevelFrame.isotIn ρ C π, q z ∈ π.S ∧
      ∀ h, q ((ρ.comp (MulAut.conj c).toMonoidHom) h z) = NG.rt D.host.E n h (q z) := by
  obtain ⟨q, hq0, hq⟩ := GlobalTheory.isotIn_detect_by_eqv_map D A ρ C π y hy hy0
  refine ⟨(NG.rt D.host.E n c⁻¹).comp q, fun h0 => hq0 ?_, fun z hz => ⟨π.stable _ _ (hq z hz).1, fun h => ?_⟩⟩
  · funext g
    have e := congrFun h0 (g * c)
    simpa [NG.rt, mul_assoc] using e
  · have e : (ρ.comp (MulAut.conj c).toMonoidHom) h = ρ (c * h * c⁻¹) := rfl
    rw [e, LinearMap.comp_apply, LinearMap.comp_apply, (hq z hz).2]
    funext g
    simp [NG.rt, mul_assoc]

theorem mem_KFix {D : D7} {s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E}
    {j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)}
    {A : Type} [AddCommGroup A] [Module ℂ A] {ρA : GAf D.host.E D.R.r →* Module.End ℂ A} {z : A} :
    z ∈ KFix D s j ρA ↔ ∀ (k : Fin 2) (v : D.nd.PlG k) (y : (GlobalTheory.GLp.red (D.host.g k) D.R.r).ker) (x : GAf D.host.E D.R.r),
      IsLiftAt (s k v) (j k v) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) x → ρA x z = z := by
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]

theorem typePrime_finiteGroup_induction_factor (D : D7) (P : G0g D.nd → Prop) (h1 : P 1)
    (hm : ∀ (g : G0g D.nd) (k : Fin 2) (v : D.nd.PlG k) (m : GL (Fin D.R.r) (ZMod (D.host.g k))), P g →
      P (GlobalTheory.GoodTypes.facHom D k v m * g)) : ∀ g, P g := by
  classical
  refine pi_ind (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) P h1 ?_
  rintro g ⟨k, v⟩ m hg
  have e : Pi.mulSingle (⟨k, v⟩ : Σ k : Fin 2, D.nd.PlG k) m = GlobalTheory.GoodTypes.facHom D k v m := by
    simp only [GlobalTheory.GoodTypes.facHom, MonoidHom.mulSingle_apply]
  rw [e]
  exact hm g k v m hg

theorem intertwine {D : D7} {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    {SA : Submodule ℂ A} {SB : Submodule ℂ B} (ρA : Representation ℂ (G0g D.nd) SA) (ρB : Representation ℂ (G0g D.nd) SB)
    (N : Submodule ℂ A) (q : A →ₗ[ℂ] B)
    (hstep : ∀ (k : Fin 2) (v : D.nd.PlG k) (m : GL (Fin D.R.r) (ZMod (D.host.g k))) (z : SA), (z : A) ∈ N →
      ((ρA (GlobalTheory.GoodTypes.facHom D k v m) z : SA) : A) ∈ N ∧ ∀ z' : SB, (z' : B) = q z →
        ((ρB (GlobalTheory.GoodTypes.facHom D k v m) z' : SB) : B) = q (ρA (GlobalTheory.GoodTypes.facHom D k v m) z)) :
    ∀ (a : MonoidAlgebra ℂ (G0g D.nd)) (z : SA) (z' : SB), (z : A) ∈ N → (z' : B) = q z →
      ((ρA.asAlgebraHom a z : SA) : A) ∈ N ∧ ((ρB.asAlgebraHom a z' : SB) : B) = q (ρA.asAlgebraHom a z) := by
  have hg : ∀ g : G0g D.nd, ∀ (z : SA) (z' : SB), (z : A) ∈ N → (z' : B) = q z →
      ((ρA g z : SA) : A) ∈ N ∧ ((ρB g z' : SB) : B) = q (ρA g z) := by
    refine typePrime_finiteGroup_induction_factor D _ ?_ ?_
    · intro z z' hz hz'
      simp only [map_one, Module.End.one_apply]
      exact ⟨hz, hz'⟩
    · intro g k v m ih z z' hz hz'
      obtain ⟨h1, h2⟩ := ih z z' hz hz'
      simp only [map_mul, Module.End.mul_apply]
      exact ⟨(hstep k v m _ h1).1, (hstep k v m _ h1).2 _ h2⟩
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    intro z z' hz hz'
    simp only [Representation.asAlgebraHom_of]
    exact hg g z z' hz hz'
  | add a c ha hc =>
    intro z z' hz hz'
    obtain ⟨a1, a2⟩ := ha z z' hz hz'
    obtain ⟨c1, c2⟩ := hc z z' hz hz'
    simp only [map_add, LinearMap.add_apply, Submodule.coe_add]
    exact ⟨N.add_mem a1 c1, by rw [a2, c2]⟩
  | smul c a ha =>
    intro z z' hz hz'
    obtain ⟨a1, a2⟩ := ha z z' hz hz'
    simp only [map_smul, LinearMap.smul_apply, Submodule.coe_smul]
    exact ⟨N.smul_mem c a1, by rw [a2]⟩

set_option maxHeartbeats 2000000 in

theorem typeVec_rows {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D}
    (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hP : GlobalTheory.Mem.R3.Pins R F cG) (I : Ident D)
    (cp : GlobalTheory.GoodTypes.Comp D) (hcp : IsComp I (fun σ => principalLevelFrame.rowRepR R.θ (Y.eFT σ)) cp) (σ : D.what₂.FT) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (x : V),
      (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧
        (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom D.ntypes.e0 x = x := by
  classical
  set π := principalLevelFrame.rowRepR R.θ (Y.eFT σ) with hπ
  have hloc := hcp σ
  choose s hs τ hτ hcpe using hloc
  have hj := fun k v => loc_piece π (s k v) (hs k v) (τ k v) (hτ k v) (I.i k v) (I.cont k v)
  choose j hjc hjP using hj
  have hinj := GlobalTheory.PlaceInj.splitPlace_v_injective D s hs
  obtain ⟨c, hA, hKc⟩ := GlobalTheory.T.rowsAtLevels_fixed_principalCongruence_typePlaces R F cG Y hP s j hs hjc
  obtain ⟨ρM, hρM⟩ := GlobalTheory.TypeAct.exists_rep D s j hinj _ ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)
  obtain ⟨ρV, hρV⟩ := GlobalTheory.TypeAct.exists_rep D s j hinj _ (rtHom D.host.E D.R.r)
  obtain ⟨b, hb⟩ := principalLevelFrame.rowRepR_occ R.θ (Y.eFT σ)
  obtain ⟨Tm, hTm, hT0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb

  have hTm' : Tm ∈ Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.toRealDat.e0 ⊓
      principalLevelFrame.isotIn (principalLevelFrame.actM Y.PY (R.MY 0)) (principalLevelFrame.Minf R.θ Y.PY (R.MY 0)) (principalLevelFrame.FinTyp.conjT π) := hTm
  obtain ⟨hG, hN⟩ := Submodule.mem_inf.1 hTm'
  have hMult : Tm ∈ Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)))
      (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) := (Submodule.mem_inf.1 hG).1
  have hK := hKc b Tm hMult
  have he := GlobalTheory.T.goodProjector_eq_goodIdempotent_typePlaces R F cG Y hP s j hs hjc c hA ρM hρM b Tm hK hG
  obtain ⟨q, hq0, hq⟩ := detect_conj (principalLevelFrame.actM Y.PY (R.MY 0)) (principalLevelFrame.Minf R.θ Y.PY (R.MY 0))
    (principalLevelFrame.FinTyp.conjT π) c Tm hN hT0

  set N := principalLevelFrame.isotIn (principalLevelFrame.actM Y.PY (R.MY 0)) (principalLevelFrame.Minf R.θ Y.PY (R.MY 0)) (principalLevelFrame.FinTyp.conjT π) with hNdef
  have hstep : ∀ (k : Fin 2) (v : D.nd.PlG k) (m : GL (Fin D.R.r) (ZMod (D.host.g k))) (z : KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)),
      (z : Mult.MMap (R.MY 0)) ∈ N →
      ((ρM (GlobalTheory.GoodTypes.facHom D k v m) z : KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)) : Mult.MMap (R.MY 0)) ∈ N ∧
      ∀ z' : KFix D s j (rtHom D.host.E D.R.r), (z' : GAf D.host.E D.R.r → ℂ) = q z →
        ((ρV (GlobalTheory.GoodTypes.facHom D k v m) z' : KFix D s j (rtHom D.host.E D.R.r)) : GAf D.host.E D.R.r → ℂ) =
          q (ρM (GlobalTheory.GoodTypes.facHom D k v m) z) := by
    intro k v m z hz
    obtain ⟨y, rfl⟩ := GlobalTheory.GLp.reduction_GL_surjective (D.host.g k) D.R.r m
    obtain ⟨x, hx1, hx2⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc D.host.E D.R.r (s k v)
      (Matrix.GeneralLinearGroup.map (j k v).toRingHom (GlobalTheory.GLp.inc _ _ y))
    have hl : IsLiftAt (s k v) (j k v) y x := ⟨hx1, hx2⟩
    have eM := hρM k v y x hl z
    refine ⟨eM ▸ isotIn_stable _ _ _ (c * x * c⁻¹) _ hz, fun z' hz' => ?_⟩
    have eV := hρV k v y x hl z'
    rw [eV, eM, hz']
    exact ((hq _ hz).2 x).symm
  have hall := intertwine ρM ρV N q hstep

  have hqK : q Tm ∈ KFix D s j (rtHom D.host.E D.R.r) := by
    rw [mem_KFix] at hK ⊢
    intro k v y x hl
    show NG.rt D.host.E D.R.r x (q Tm) = q Tm
    rw [← (hq _ hN).2 x, hK k v y x hl]
  refine ⟨KFix D s j (rtHom D.host.E D.R.r), inferInstance, inferInstance, ρV,
    (principalLevelFrame.FinTyp.conjT π).S.comap (KFix D s j (rtHom D.host.E D.R.r)).subtype, ⟨q Tm, hqK⟩, ?_, ?_, ?_, ?_⟩
  · intro k v
    rw [hcpe k v]
    intro yv hyv hyv0
    have hf : conjL (yv : GAf D.host.E D.R.r → ℂ) ∈ π.S := hyv
    have hf0 : conjL (yv : GAf D.host.E D.R.r → ℂ) ≠ 0 := by
      intro h0
      apply hyv0
      apply Subtype.ext
      funext g
      have := congrFun h0 g
      simpa [conjL] using this
    obtain ⟨p, hp0, hpe⟩ := hjP k v _ hf hf0
    refine ⟨p.comp (conjL.comp (KFix D s j (rtHom D.host.E D.R.r)).subtype), hp0, fun z hz => ⟨?_, fun h => ?_⟩⟩
    · have hzf : conjL (z : GAf D.host.E D.R.r → ℂ) ∈ π.S := hz
      simp only [GlobalTheory.GLp.fixK1, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
        sub_eq_zero]
      intro k1
      obtain ⟨x, hx1, hx2⟩ := GlobalTheory.SplitSec.exists_trivOutside_loc D.host.E D.R.r (s k v)
        (Matrix.GeneralLinearGroup.map (j k v).toRingHom (GlobalTheory.GLp.inc _ _ (k1 : GL (Fin D.R.r) ℤ_[D.host.g k])))
      have hl : IsLiftAt (s k v) (j k v) (k1 : GL (Fin D.R.r) ℤ_[D.host.g k]) x := ⟨hx1, hx2⟩
      have hzK : NG.rt D.host.E D.R.r x (z : GAf D.host.E D.R.r → ℂ) = z := (mem_KFix.1 z.2) k v k1 x hl
      have e1 := hpe (k1 : GL (Fin D.R.r) ℤ_[D.host.g k]) x hl _ hzf
      have e2 : NG.rt D.host.E D.R.r x (conjL (z : GAf D.host.E D.R.r → ℂ)) = conjL (z : GAf D.host.E D.R.r → ℂ) := by
        have e3 : NG.rt D.host.E D.R.r x (conjL (z : GAf D.host.E D.R.r → ℂ)) =
            conjL (NG.rt D.host.E D.R.r x (z : GAf D.host.E D.R.r → ℂ)) := rfl
        rw [e3, hzK]
      rw [e2] at e1
      exact e1.symm
    · have hzf : conjL (z : GAf D.host.E D.R.r → ℂ) ∈ π.S := hz
      have hy0 : GlobalTheory.GLp.red (D.host.g k) D.R.r (Function.invFun (GlobalTheory.GLp.red (D.host.g k) D.R.r) h) = h :=
        Function.invFun_eq (GlobalTheory.GLp.reduction_GL_surjective (D.host.g k) D.R.r h)
      obtain ⟨x, hl⟩ : ∃ x, IsLiftAt (s k v) (j k v) (Function.invFun (GlobalTheory.GLp.red (D.host.g k) D.R.r) h) x :=
        GlobalTheory.SplitSec.exists_trivOutside_loc D.host.E D.R.r (s k v) _
      have eV := hρV k v _ x hl z
      rw [hy0] at eV
      have e1 := hpe _ x hl _ hzf
      exact (congrArg (fun f => p (conjL f)) eV).trans e1
  · intro h0
    apply hq0
    exact congrArg Subtype.val h0
  · intro a
    obtain ⟨h1, h2⟩ := hall a ⟨Tm, hK⟩ ⟨q Tm, hqK⟩ hN rfl
    show ((ρV.asAlgebraHom a ⟨q Tm, hqK⟩ : KFix D s j (rtHom D.host.E D.R.r)) : GAf D.host.E D.R.r → ℂ) ∈
      (principalLevelFrame.FinTyp.conjT π).S
    rw [h2]
    exact (hq _ h1).1
  · apply Subtype.ext
    obtain ⟨-, h2⟩ := hall D.ntypes.e0 ⟨Tm, hK⟩ ⟨q Tm, hqK⟩ hN rfl
    rw [h2, he]

section Target

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem typeVec : PrN → OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (I : GlobalTheory.TypeRec.Ident (w.st Z).toD7) cp, GlobalTheory.TypeRec.IsComp I (repOf Y) cp → ∀ σ, ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ (G0g (w.st Z).toD7.nd) V) (W : Submodule ℂ V) (x : V), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom (w.st Z).toD7 k v) (cp σ k v).ρ) ∧ x ≠ 0 ∧ (∀ a, ρ.asAlgebraHom a x ∈ W) ∧ ρ.asAlgebraHom (w.st Z).toD7.ntypes.e0 x = x := by
  intro _
  refine ⟨1, one_pos, ?_⟩
  intro eps C8 C5 c6 Cb _ _ _ _
  refine ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ => ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, ?_⟩
  intro B f T _ _ _ _ _ w _ Z Wt hX z p0 Y _ _ _ _ _ I cp hcp σ
  exact typeVec_rows z.R z.F z.cG Y z.pins I cp hcp σ

end Target

end GlobalTheory.TypeVec

end
