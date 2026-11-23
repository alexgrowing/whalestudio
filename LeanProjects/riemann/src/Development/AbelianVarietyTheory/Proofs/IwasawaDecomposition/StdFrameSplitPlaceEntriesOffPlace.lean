import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameComponentEqOneOffSplitPlaceOfTrivOutsideStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardFrameConjugateCloseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateIntoK1Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlaceOverSplitPlaceEqChosenOrConjugateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLevelSplit

theorem lemB_pf : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (x : GA D V), L.Pg ⊆ T → L.Q ⊆ T → x ∈ GfC V → finE V x ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T → x ∈ levS V β L ∧ levChi V β L x = 1 := by
  intro D V β L T x hg hq hx hK
  have h3 : ∀ PP ∈ T, Formalism.L2.DIV.redFn β PP (finE V x) = 1 := by
    have h1 : finE V x ∈ ⨅ PP ∈ T, Formalism.L2.DIV.princAt β PP := hK.2
    exact fun PP hP => (Formalism.L2.DIV.mem_princAt.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h1 PP) hP)).2
  refine ⟨⟨hx, Formalism.L2.DIV.Kg_le_lev hg hq hK⟩, ?_⟩
  have hr : Formalism.L2.DIV.rTup β L (finE V x) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock L.hr (Formalism.L2.DIV.redFn β PP.1 (finE V x)) = 1
    rw [h3 PP.1 (hg PP.2)]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  unfold levChi Formalism.L2.DIV.levFn
  rw [hr, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
  · rfl
  · intro PP hP
    rw [h3 PP (hq hP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]
  · intro PP hP
    refine Finset.prod_eq_one fun c _ => ?_
    rw [h3 PP (hg hP), Formalism.L2.DIV.dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one]

theorem int_of_lt {D : D7} {n : ℕ} (y : Matrix (Fin n) (Fin n) (EAf D))
    (h : ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin n), Valued.v (GlobalTheory.StdFrames.cpt Q (y a b - (1 : Matrix (Fin n) (Fin n) (EAf D)) a b)) < 1)
    (a b : Fin n) : y a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  have h1 : (1 : Matrix (Fin n) (Fin n) (EAf D)) a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  have h2 : y a b - (1 : Matrix (Fin n) (Fin n) (EAf D)) a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    (GlobalTheory.AdIsom.mem_OA _).2 fun Q => le_of_lt (h Q a b)
  have := add_mem h2 h1
  rwa [sub_add_cancel] at this

set_option maxHeartbeats 2000000 in
theorem glInt_of_int {D : D7} {n : ℕ} (y : GL (Fin n) (EAf D))
    (i1 : ∀ a b, y.val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i2 : ∀ a b, (y⁻¹).val a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    ∃ z : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E), Formalism.L2.DIV.intGL D.host.F D.host.E n z = y ∧
      ∀ a b, ((z.val a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = y.val a b := by
  let φ : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) →+* Matrix (Fin n) (Fin n) (EAf D) :=
    RingHom.mapMatrix (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype
  have inj : Function.Injective φ := fun M N h => Matrix.ext fun a b => Subtype.ext (congrFun (congrFun h a) b)
  let zM : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) := Matrix.of fun a b => ⟨_, i1 a b⟩
  let zI : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E) := Matrix.of fun a b => ⟨_, i2 a b⟩
  have e1 : φ zM = y.val := by ext a b; rfl
  have e2 : φ zI = (y⁻¹).val := by ext a b; rfl
  have m1 : zM * zI = 1 := inj (show φ (zM * zI) = φ 1 by rw [map_mul, map_one, e1, e2, Units.mul_inv])
  have m2 : zI * zM = 1 := inj (show φ (zI * zM) = φ 1 by rw [map_mul, map_one, e1, e2, Units.inv_mul])
  exact ⟨⟨zM, zI, m1, m2⟩, Units.ext e1, fun a b => rfl⟩

set_option maxHeartbeats 800000 in
theorem kg_of_cpt : ∀ (D : D7) (V : HSp D) (β x : GL (Fin V.rank) (EAf D)) (T : Finset (Formalism.L2.DIV.Pl D.host.E)), x ∈ Formalism.L2.DIV.UA D.sp.cm V.gram → (∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * x * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → (∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * x⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → x ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T := by
  intro D V β x T hU h1 h2
  have hyi : (β⁻¹ * x * β)⁻¹ = β⁻¹ * x⁻¹ * β := by group
  have i1 := int_of_lt (β⁻¹ * x * β).val h1
  have i2 := int_of_lt ((β⁻¹ * x * β)⁻¹).val (by rw [hyi]; exact h2)
  obtain ⟨z, hz0, hzv⟩ := glInt_of_int (β⁻¹ * x * β) i1 i2
  have hz : Formalism.L2.DIV.frGL β z = x := by
    show β * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank z * β⁻¹ = x
    rw [hz0]; group
  have hS : x ∈ Formalism.L2.DIV.St β := ⟨z, hz⟩
  have hred : ∀ PP, Formalism.L2.DIV.redFn β PP x = 1 := by
    intro PP
    rw [← hz, Formalism.L2.DIV.redFn_frGL]
    apply Units.ext
    ext a b
    show Formalism.L2.DIV.resS D.host.F PP (z.val a b) = (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.DIV.kP PP)) a b
    have h0 : Formalism.L2.DIV.resS D.host.F PP (z.val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b) = 0 := by
      rw [GlobalTheory.AdIsom.resS_eq_zero_iff_cpt]
      have e3 : ((z.val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E)) a b : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
          (β⁻¹ * x * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b := by
        rw [← hzv a b, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> rfl
      rw [e3]; exact h1 PP a b
    rw [map_sub, sub_eq_zero] at h0
    rw [h0, Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
  exact ⟨⟨hU, hS⟩, Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun _ => Formalism.L2.DIV.mem_princAt.2 ⟨hS, hred PP⟩⟩

theorem trivOutside_inv {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {T : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {x : Formalism.AUTREP.GAf L n} (hx : TrivOutside T x) : TrivOutside T x⁻¹ := fun v hv => by
  have h1 : (((x⁻¹ : Formalism.AUTREP.GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
  have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
  simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  exact h2

theorem lemA_pf (hC2 : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ T : Finset (Formalism.L2.DIV.Pl D.host.E), finE V (P.ψ κ) ∈ Formalism.L2.DIV.Kg D.sp.cm V.gram β T := by
  intro D V n hF P β Λ N hS hβ s
  obtain ⟨h, hh⟩ := hC2 D V n hF P β Λ N hS hβ s
  refine ⟨h, fun κ hκ hk T => ?_⟩
  have hk' : h⁻¹ * s.loc n κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) := by
    have := Subgroup.inv_mem _ hk
    rwa [show (h⁻¹ * s.loc n κ * h)⁻¹ = h⁻¹ * (s.loc n κ)⁻¹ * h by group, ← map_inv] at this
  have e : finE V (P.ψ κ⁻¹) = (finE V (P.ψ κ))⁻¹ := by rw [map_inv, map_inv]
  refine kg_of_cpt D V β (finE V (P.ψ κ)) T (GlobalTheory.LevSplit.finE_mem_UA V _) (hh κ hκ hk) ?_
  have := hh κ⁻¹ (trivOutside_inv hκ) hk'
  rwa [e] at this

theorem stdFrame_splitPlace_entries_off_place (hA : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E) (κ : Formalism.AUTREP.GAf D.host.E n), TrivOutside {s.v} κ → ∀ (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) ≠ s.v.asIdeal → ∀ (a b : Fin V.rank), GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b) = GlobalTheory.StdFrames.cpt Q ((1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) (hC : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) (hDd : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) (hE : ∀ (D : D7), D.host.F = maximalRealSubfield D.host.E → ∀ (s : SplitPlace D.host.E) (Q : Formalism.L2.DIV.Pl D.host.E), Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal → Q = s.w ∨ Q = GlobalTheory.IdemSupport.cP s.w) : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), GlobalTheory.Mem.R3.StdFrame hF P → IsSDFrame V β Λ N → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ (Q : Formalism.L2.DIV.Pl D.host.E) (a b : Fin V.rank), Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V n hF P β Λ N hS hβ s
  obtain ⟨h, hh⟩ := hDd D V n hF P β hS s
  refine ⟨h, fun κ hκ hk Q a b => ?_⟩
  by_cases hQ : Q.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) = s.v.asIdeal
  · rcases hE D hF s Q hQ with rfl | rfl
    · exact hh κ hκ hk a b
    · have hk' : h⁻¹ * s.loc n κ⁻¹ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) := by
        have := Subgroup.inv_mem _ hk
        rwa [show (h⁻¹ * s.loc n κ * h)⁻¹ = h⁻¹ * (s.loc n κ)⁻¹ * h by group, ← map_inv] at this
      refine hC D V β Λ N hβ (P.ψ κ) s.w (fun a b => ?_) a b
      have := hh κ⁻¹ (trivOutside_inv hκ) hk' a b
      rwa [map_inv, map_inv] at this
  · rw [map_sub, hA D V n hF P β hS s κ hκ Q hQ a b, sub_self, map_zero]
    exact zero_lt_one

theorem levS_of_kOne_conj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E), s.w = D.naut.plGw k v → ∃ h : GL (Fin D.R.r) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ (b : Bool) (κ : Formalism.AUTREP.GAf D.host.E D.R.r), TrivOutside {s.v} κ → h⁻¹ * s.loc D.R.r κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin D.R.r) → Y.PY.ψ κ ∈ levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) ∧ levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b)) (Y.PY.ψ κ) = 1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost k v s hs
  have hβ := hP.char.base.lev.βY 0 Y.hm
  obtain ⟨h, hh⟩ := lemA_pf (stdFrame_splitPlace_entries_off_place GlobalTheory.T.frameComponent_eq_one_off_splitPlace_of_trivOutside GlobalTheory.T.standard_frame_conjugate_close GlobalTheory.T.exists_conjugate_into_K1 GlobalTheory.T.placeOver_splitPlace_eq_chosen_or_conjugate) D (Yc D 0) D.R.r Y.hF Y.PY (R.βY 0) _ _
    Y.stdPsi.1 hβ s
  refine ⟨h, fun b κ hκ hk => ?_⟩
  classical
  exact lemB_pf D (Yc D 0) (R.βY 0) _ (_ ∪ _) (Y.PY.ψ κ) Finset.subset_union_left Finset.subset_union_right (Y.PY.into κ)
    (hh κ hκ hk _)

end GlobalTheory.RowLevelSplit
