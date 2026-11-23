import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MainEqSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldMemLevelOfCoprime

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.Pf.MainEqCut
  Formalism.L2.SG.Pf.MainEqSteps

namespace Formalism.L2.SG.Pf.MainEqClass

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def PairOfRowC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    ∀ t₁ t₂ : TauC Y u u, t₁ ∈ (Y.tO u u).genSet → t₂ ∈ (Y.tO u u).genSet →
      (Y.tO u u).rowOf t₁ = (Y.tO u u).rowOf t₂ →
      IsPair t₁.lam (lf D (X.Fu u)) t₁.frame t₂.frame (t₂.lin * t₁.lin⁻¹) (gS D)

def LiftIotaEqC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), ConcTie X Y →
    ∀ s₁ s₂ : TauC Y u u, s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic →
      (Y.tO u u).rowOf s₁ = (Y.tO u u).rowOf s₂ →
        IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D)

def GUnramC : Prop :=
  ∀ D : D7, ∀ i, Formalism.L2.SG.LemmaN.Unram D.host.E (D.host.g i)

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem gmap_mul' (a b : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [← Submodule.map_comp]
  rfl

theorem gmap_one' (L : Submodule (𝓞 E) S.V) : Formalism.HermitianLatticesTheory.gmap (1 : S.V ≃ₗ[E] S.V) L = L := by
  unfold Formalism.HermitianLatticesTheory.gmap
  ext x
  simp

theorem gmap_inv_of' {a : S.V ≃ₗ[E] S.V} {L L' : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap a L' = L) :
    Formalism.HermitianLatticesTheory.gmap a⁻¹ L = L' := by
  rw [← h, ← gmap_mul', inv_mul_cancel, gmap_one']

theorem xflag_mapLF' {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) (j : ℕ) :
    Xflag (mapLF γ F) j = (Xflag F j).map (γ : S.V →ₗ[E] S.V) := by
  unfold Xflag mapLF
  rw [dif_pos hγ]
  show (mapFlag γ hγ F.fl).Xa j = _
  unfold FlagG.Xa mapFlag
  try simp only [Submodule.map_span, Set.image_image]
  try rfl

theorem z_mapLF' {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    (mapLF γ F).fl.z = γ F.fl.z := by
  unfold mapLF
  rw [dif_pos hγ]
  try rfl

theorem isPair_quot' {T T' : E} (Λ Λ' : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (γ₁ γ₂ : S.V ≃ₗ[E] S.V) (h₁ : γ₁ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h₂ : γ₂ ∈ Formalism.HermitianLatticesTheory.isom S.hT)
    (hl₁ : Formalism.HermitianLatticesTheory.gmap γ₁ Λ' = Λ) (hl₂ : Formalism.HermitianLatticesTheory.gmap γ₂ Λ' = Λ)
    (hι : IotaCompat Λ F (mapLF γ₁ F') (mapLF γ₂ F') (γ₂ * γ₁⁻¹) g) :
    IsPair Λ F (mapLF γ₁ F') (mapLF γ₂ F') (γ₂ * γ₁⁻¹) g := by
  unfold IsPair
  refine ⟨?_, ?_, ?_, hι⟩
  · unfold IsAutLam
    refine ⟨(Formalism.HermitianLatticesTheory.isom S.hT).mul_mem h₂ ((Formalism.HermitianLatticesTheory.isom S.hT).inv_mem h₁), ?_⟩
    rw [gmap_mul', gmap_inv_of' hl₁, hl₂]
  · intro j
    rw [xflag_mapLF' γ₁ h₁, xflag_mapLF' γ₂ h₂, ← Submodule.map_comp]
    congr 1
    ext x
    simp
  · rw [z_mapLF' γ₁ h₁, z_mapLF' γ₂ h₂]
    simp

end Gen

section Pf

variable {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)

def carr (t : TauC Y u u) : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u) := ⟨t.frame, t.rep.2.2.2.2⟩

theorem gval_ne (t : TauC Y u u) (ht : t ∈ (Y.tO u u).genSet) : Gval (lf D (X.Fu u)) t.frame ≠ 0 := by
  have h : (Y.tO u u).G t ≠ 0 := ht.1
  change Formalism.L2.SG.TermOp.Gt t ≠ 0 at h
  unfold Formalism.L2.SG.TermOp.Gt at h
  have hG : t.G ≠ 0 := fun h0 => h (if_pos h0)
  have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u (X.Fu u) t.lam hrow).1
  have hmk := Formalism.L2.SG.TermDef.Gt_mk hGF ⟨t.frame, t.rep.2.2.2.2⟩
  intro h0
  apply hG
  show Formalism.L2.SG.TermDef.Gt _ _ _ (Formalism.L2.SG.TermDef.mk _ _ _ ⟨t.frame, t.rep.2.2.2.2⟩) = 0
  rw [hmk]
  exact h0

theorem lam_eq {t t' : TauC Y u u} (h : (Y.tO u u).rowOf t = (Y.tO u u).rowOf t') : t.lam = t'.lam := by
  have h2 := congrArg Prod.fst h
  exact congrArg Subtype.val h2

theorem lam'_eq {t t' : TauC Y u u} (h : (Y.tO u u).rowOf t = (Y.tO u u).rowOf t') : t.lam' = t'.lam' := by
  have h2 := congrArg Prod.fst (congrArg Prod.snd h)
  exact congrArg Subtype.val h2

theorem pairOfRowC_of (h : LiftIotaEqC) : PairOfRowC := by
  intro D X Y u hc t₁ t₂ h₁ h₂ hr
  have hG : ∀ t : TauC Y u u, t ∈ (Y.tO u u).genSet → t.G ≠ 0 ∧ t.generic := by
    intro t ht
    obtain ⟨hg, hgen⟩ := ht
    refine ⟨fun h0 => hg ?_, hgen⟩
    show Gt t = 0
    simp [Gt, h0]
  obtain ⟨g1, e1⟩ := hG t₁ h₁
  obtain ⟨g2, e2⟩ := hG t₂ h₂
  have hι := h D X Y u hc t₁ t₂ g1 g2 e1 e2 hr
  have hl₁ : Formalism.HermitianLatticesTheory.gmap t₁.lin t₁.lam' = t₁.lam := t₁.rep.2.2.2.1
  have hl₂ : Formalism.HermitianLatticesTheory.gmap t₂.lin t₁.lam' = t₁.lam := by
    rw [lam'_eq Y u hr, lam_eq Y u hr]
    exact t₂.rep.2.2.2.1
  exact isPair_quot' t₁.lam t₁.lam' (gS D) (lf D (X.Fu u)) (lf D (X.Fu u)) t₁.lin t₂.lin
    t₁.rep.2.2.1 t₂.rep.2.2.1 hl₁ hl₂ hι

end Pf

end Formalism.L2.SG.Pf.MainEqClass

namespace Formalism.L2.SG.Pf

open Formalism.L2.SG.Pf.MainEqClass

theorem stepClassG_of_pair_unram (hP : PairOfRowC) (hU : GUnramC) : StepClassG := by
  intro D X Y u h3 hT
  have hBF := Formalism.L2.SG.Closed.BetaFree_holds D u u (fun i => ⟨h3 i, hU D i⟩)
  refine ⟨fun t ht => ?_, fun t ht t' ht' hr h1 h2 => ?_,
    fun t ht t' ht' t'' ht'' hr1 hr2 h1 h2 h3 h4 => ?_⟩
  ·
    have hΛ := (Y.rowsOK u).1 t.lam t.mem
    have hg := gval_ne Y u t ht
    obtain ⟨β, hp, hs, hsc⟩ := (Formalism.L2.SG.Closed.ScalarEquiv_holds D u u (X.Fu u) t.lam hΛ).refl ⟨carr Y u t, hg⟩
    have hp0 := hP D X Y u hT t t ht ht rfl
    obtain ⟨e1, e2⟩ := hBF (X.Fu u) t.lam hΛ (carr Y u t) (carr Y u t) hg hg β _ hp hp0
    show s0T t t = 1 ∧ scalT t t
    unfold s0T scalT
    rw [if_pos ⟨rfl, rfl⟩]
    refine ⟨?_, ⟨rfl, rfl⟩, ?_, ?_⟩
    · exact e1.symm.trans hs
    · exact e1.symm.trans hs
    · exact e2.1 hsc
  ·
    have hl := lam_eq Y u hr
    have hl' := lam'_eq Y u hr
    have hΛ := (Y.rowsOK u).1 t.lam t.mem
    have hg := gval_ne Y u t ht
    have hg' := gval_ne Y u t' ht'
    obtain ⟨-, hs, hsc⟩ := (show scalT t t' from h2)
    have hPD' : TermDef.PD D t.lam (lf D (X.Fu u)) u t'.frame := hl ▸ t'.rep.2.2.2.2
    set y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u) := ⟨t'.frame, hPD'⟩
    have a : Formalism.L2.SG.Corank.ScalRelD D u (X.Fu u) t.lam ⟨carr Y u t, hg⟩ ⟨y, hg'⟩ :=
      ⟨_, hP D X Y u hT t t' ht ht' hr, hs, hsc⟩
    obtain ⟨β, hp, hs2, hsc2⟩ := (Formalism.L2.SG.Closed.ScalarEquiv_holds D u u (X.Fu u) t.lam hΛ).symm a
    have hp0 := hP D X Y u hT t' t ht' ht hr.symm
    rw [← hl] at hp0
    obtain ⟨e1, e2⟩ := hBF (X.Fu u) t.lam hΛ y (carr Y u t) hg' hg β _ hp hp0
    show s0T t' t = 1 ∧ scalT t' t
    unfold s0T scalT
    rw [if_pos ⟨hl.symm, hl'.symm⟩, ← hl]
    refine ⟨?_, ⟨rfl, hl'.symm⟩, ?_, ?_⟩
    · exact e1.symm.trans hs2
    · exact e1.symm.trans hs2
    · exact e2.1 hsc2
  ·
    have hl := lam_eq Y u hr1
    have hl2 := lam_eq Y u hr2
    have hl' := lam'_eq Y u hr1
    have hl2' := lam'_eq Y u hr2
    have hΛ := (Y.rowsOK u).1 t.lam t.mem
    have hg := gval_ne Y u t ht
    have hg' := gval_ne Y u t' ht'
    have hg'' := gval_ne Y u t'' ht''
    obtain ⟨-, hs1, hsc1⟩ := (show scalT t t' from h2)
    obtain ⟨-, hs2, hsc2⟩ := (show scalT t' t'' from h4)
    have hPD' : TermDef.PD D t.lam (lf D (X.Fu u)) u t'.frame := hl ▸ t'.rep.2.2.2.2
    have hPD'' : TermDef.PD D t.lam (lf D (X.Fu u)) u t''.frame := (hl.trans hl2) ▸ t''.rep.2.2.2.2
    set y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u) := ⟨t'.frame, hPD'⟩
    set z : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u) := ⟨t''.frame, hPD''⟩
    have a : Formalism.L2.SG.Corank.ScalRelD D u (X.Fu u) t.lam ⟨carr Y u t, hg⟩ ⟨y, hg'⟩ :=
      ⟨_, hP D X Y u hT t t' ht ht' hr1, hs1, hsc1⟩
    have hp2 := hP D X Y u hT t' t'' ht' ht'' hr2
    rw [← hl] at hp2 hs2 hsc2
    have b : Formalism.L2.SG.Corank.ScalRelD D u (X.Fu u) t.lam ⟨y, hg'⟩ ⟨z, hg''⟩ := ⟨_, hp2, hs2, hsc2⟩
    obtain ⟨β, hp, hs3, hsc3⟩ := (Formalism.L2.SG.Closed.ScalarEquiv_holds D u u (X.Fu u) t.lam hΛ).trans a b
    have hp0 := hP D X Y u hT t t'' ht ht'' (hr1.trans hr2)
    obtain ⟨e1, e2⟩ := hBF (X.Fu u) t.lam hΛ (carr Y u t) z hg hg'' β _ hp hp0
    show s0T t t'' = 1 ∧ scalT t t''
    unfold s0T scalT
    rw [if_pos ⟨hl.trans hl2, hl'.trans hl2'⟩]
    refine ⟨?_, ⟨hl.trans hl2, hl'.trans hl2'⟩, ?_, ?_⟩
    · exact e1.symm.trans hs3
    · exact e1.symm.trans hs3
    · exact e2.1 hsc3

theorem gUnramC_holds : GUnramC := by
  intro D i Q _ _
  have hp := D.host.g_prime i
  have : Fact (D.host.g i).Prime := ⟨hp⟩
  have hc : (Ideal.primesOver (Ideal.span {((D.host.g i : ℕ) : ℤ)}) (𝓞 D.host.E)).ncard =
      Module.finrank ℚ D.host.E :=
    (Formalism.MainNotions.Inhab.primesOver_ncard D.host.E (D.host.g i) hp).trans (D.nd.g_split i)
  have : Fintype ((Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.E)) :=
    (Algebra.QuasiFinite.finite_primesOver (Ideal.span {((D.host.g i : ℕ) : ℤ)})).fintype
  have hs := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {((D.host.g i : ℕ) : ℤ)}) (𝓞 D.host.E)
  rw [RingOfIntegers.rank] at hs
  have hcard : Fintype.card ((Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.E)) =
      Module.finrank ℚ D.host.E := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hc]
  have hpos : ∀ q : (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.E),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    rintro ⟨q, h1, h2⟩
    exact Nat.mul_pos (Ideal.ramificationIdx_pos q ℤ) (Ideal.inertiaDeg_pos q ℤ)
  have hall : ∀ q : (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.E),
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = 1 := by
    intro q0
    by_contra hne
    have h2 : 2 ≤ q0.1.ramificationIdx ℤ * q0.1.inertiaDeg ℤ := by
      have := hpos q0; omega
    have hsum := Finset.add_sum_erase Finset.univ
      (fun q : (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.E) =>
        q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) (Finset.mem_univ q0)
    have hrest : (Finset.univ.erase q0).card ≤ ∑ q ∈ Finset.univ.erase q0, q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
      have := Finset.sum_le_sum (s := Finset.univ.erase q0) (fun q _ => hpos q)
      simpa using this
    have hcard2 : (Finset.univ.erase q0).card + 1 = Fintype.card
        ((Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.E)) := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ q0), Finset.card_univ]
      have : 0 < Fintype.card ((Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.E)) :=
        Fintype.card_pos_iff.2 ⟨q0⟩
      omega
    omega
  have hQ : Q ∈ (Ideal.span {((D.host.g i : ℕ) : ℤ)}).primesOver (𝓞 D.host.E) := ⟨inferInstance, inferInstance⟩
  have := hall ⟨Q, hQ⟩
  exact Nat.eq_one_of_mul_eq_one_right this

theorem stepClassG_of_pair (hP : PairOfRowC) : StepClassG := stepClassG_of_pair_unram hP gUnramC_holds

theorem stepClassG_of_liftIota (h : LiftIotaEqC) : StepClassG :=
  stepClassG_of_pair (pairOfRowC_of h)

end Formalism.L2.SG.Pf
