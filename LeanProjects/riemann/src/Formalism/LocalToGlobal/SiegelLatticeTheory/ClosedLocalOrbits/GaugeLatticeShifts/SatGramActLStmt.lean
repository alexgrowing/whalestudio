import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGram
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SatGramActRRep

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.NormCut Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.Pf.SatGramActL

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def LeftActC' : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    ∀ S ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))),
    Formalism.L2.SG.Pf.SatGram.LeftAct (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') S
      (Aset Y.TR (Y.cs u))

def kB {D : D7} {X : HidaSetting D} {w : D.what₂.Word} {rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (c : ColSys X w rs) (Λ : Submodule (𝓞 D.host.E) (VS D).V) (γ : Gam X w) : X.B.I.Gf :=
  ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w)⁻¹ * (iotaF X w γ : X.B.I.Gf) * ((c.h (c.base Λ) : X.B.I.Gf) * X.xu w)

def kBB {D : D7} {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (x : X.B.I.GA) : X.B.I.Gf :=
  kOf X u u' ((Y.cs u).h ((Y.cs u).base Λ) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base Λ') : X.B.I.Gf) x

def BetaLift : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (w : D.what₂.Word) (rs : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (c : ColSys X w rs)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), Λ ∈ rs → ∀ γ : Gam X w, kB c Λ γ ∈ X.B.I.Kset →
    ∃ β : (VS D).V ≃ₗ[D.host.E] (VS D).V, RatLink X (γ : X.B.I.GA) β ∧ β ∈ Saturated.AutF Λ (lf D (X.Fu w))

def SMemLeft : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t t' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    β ∈ Saturated.AutF t.lam (lf D (X.Fu u)) → t'.lam = t.lam → t'.lam' = t.lam' →
    (∃ n ∈ NLam t.lam (lf D (X.Fu u)), ∃ n' ∈ NLam t.lam' (lf D (X.Fu u')), t'.lin = n * (β * t.lin) * n') →
    ∀ S ∈ ({(Y.tO u u').genSet, (Y.tO u u').ngSet, (Y.tO u u').degSet} :
      Set (Set (GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')))), t ∈ S → t' ∈ S

def IotaLeft : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (γ : Gam X u), kB (Y.cs u) t.lam γ ∈ X.B.I.Kset →
      levi Y.TR (kB (Y.cs u) t.lam γ * kBB Y u u' t.lam t.lam' t.rep.1.1) =
        levi Y.TR (kB (Y.cs u) t.lam γ) * levi Y.TR (kBB Y u u' t.lam t.lam' t.rep.1.1)

def ChiNLeft : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V),
    Λ ∈ Y.what₂ u → Λ' ∈ Y.what₂ u' → ∀ γ : Gam X u, kB (Y.cs u) Λ γ ∈ X.B.I.Kset →
    ∀ p : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ',
      chiN X (kB (Y.cs u) Λ γ * kBB Y u u' Λ Λ' p.1.1) = chiN X (kBB Y u u' Λ Λ' p.1.1)

def OOLeft : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (s : X.B.I.Ginf), s ∈ Hinf X u →
    ∀ (Ω : Set X.B.I.Ginf) (y : X.B.I.Ginf), MeasurableSet Ω →
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       OO (Formalism.L2.SG.ProjRows.muInf X.B.I) ((fun x => s⁻¹ * x) ⁻¹' Ω) (X.Wu u) (X.Wu u') (s * y)) =
      (X.piU u s).comp (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
        OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') y)

def FundConj : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) (x0 : X.B.I.GA)
    (β γ : (VS D).V ≃ₗ[D.host.E] (VS D).V), RatLink X x0 β → β ∈ Saturated.AutF Λ (lf D (X.Fu u)) →
    ∀ Ω : Set X.B.I.Ginf, IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' γ) Ω →
      IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' (β * γ)) ((fun x => x0.1⁻¹ * x) ⁻¹' Ω)

section NC

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {Λ : Submodule (𝓞 E) S.V}
  {r : ℕ} {T : E} {F : LFlag S r T}

theorem fix_e {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) (i : Fin r) : β (F.fl.e i) = F.fl.e i := by
  obtain ⟨-, hf, -⟩ := hβ
  have h := hf (Fin.castSucc i)
  unfold frame at h
  have hh : F.fl.fvec i.castSucc = F.fl.e i := by
    unfold FlagG.fvec
    simp
  exact hh ▸ h

theorem fix_xflag {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) (j : ℕ) : ∀ x ∈ Xflag F j, β x = x := by
  intro x hx
  unfold Xflag FlagG.Xa at hx
  have hle : Submodule.span E (F.fl.e '' {i | ↑i < j}) ≤
      LinearMap.eqLocus (β : S.V →ₗ[E] S.V) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    simpa [LinearMap.mem_eqLocus] using fix_e hβ i
  have h2 := hle hx
  simpa [LinearMap.mem_eqLocus] using h2

theorem fix_xsp {β : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) : ∀ x ∈ Xsp F, β x = x := by
  intro x hx
  unfold Xsp FlagG.X at hx
  have hle : Submodule.span E (Set.range F.fl.e) ≤
      LinearMap.eqLocus (β : S.V →ₗ[E] S.V) LinearMap.id := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    simpa [LinearMap.mem_eqLocus] using fix_e hβ i
  have h2 := hle hx
  simpa [LinearMap.mem_eqLocus] using h2

theorem inv_fix {β : S.V ≃ₗ[E] S.V} {x : S.V} (h : β x = x) : β⁻¹ x = x := by
  calc β⁻¹ x = β⁻¹ (β x) := by rw [h]
    _ = x := by rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl

theorem nlam_conj {β n : S.V ≃ₗ[E] S.V} (hβ : β ∈ Saturated.AutF Λ F) (hn : n ∈ NLam Λ F) :
    β * n * β⁻¹ ∈ NLam Λ F := by
  unfold NLam at hn ⊢
  obtain ⟨hA, hF, hX⟩ := hn
  have hB := hβ
  unfold Saturated.AutF at hB
  obtain ⟨hBA, -, -⟩ := hB
  unfold IsAutLam at hA hBA
  obtain ⟨hAi, hAg⟩ := hA
  obtain ⟨hBi, hBg⟩ := hBA
  have hmap : ∀ (a b : S.V ≃ₗ[E] S.V) (L : Submodule (𝓞 E) S.V),
      HermitianLatticesTheory.gmap (a * b) L = HermitianLatticesTheory.gmap a (HermitianLatticesTheory.gmap b L) := by
    intro a b L
    unfold HermitianLatticesTheory.gmap
    rw [← Submodule.map_comp]
    rfl
  have hone : ∀ L : Submodule (𝓞 E) S.V, HermitianLatticesTheory.gmap (1 : S.V ≃ₗ[E] S.V) L = L := by
    intro L
    unfold HermitianLatticesTheory.gmap
    have h1 : ((1 : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V).restrictScalars (𝓞 E) = LinearMap.id :=
      LinearMap.ext fun _ => rfl
    rw [h1, Submodule.map_id]
  have hBinv : HermitianLatticesTheory.gmap β⁻¹ Λ = Λ := by
    calc HermitianLatticesTheory.gmap β⁻¹ Λ = HermitianLatticesTheory.gmap β⁻¹ (HermitianLatticesTheory.gmap β Λ) := by rw [hBg]
      _ = Λ := by rw [← hmap, inv_mul_cancel, hone]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact mul_mem (mul_mem hBi hAi) (inv_mem hBi)
  · rw [hmap, hmap, hBinv, hAg, hBg]
  · intro j x hx
    have hx1 : β x = x := fix_xflag hβ (j + 1) x hx
    have hxi : β⁻¹ x = x := inv_fix hx1
    have hd := hF j x hx
    have hfix : β (n x - x) = n x - x := fix_xflag hβ j _ hd
    have hc : (β * n * β⁻¹) x - x = β (n x - x) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hxi, map_sub, hx1]
    rw [hc, hfix]
    exact hd
  · intro x hx
    have hiso : ∀ a b, S.hT (β a) (β b) = S.hT a b := hBi
    have hxo : ∀ v ∈ Xsp F, S.hT v x = 0 := by
      intro v hv
      unfold orth at hx
      have h1 := (Submodule.mem_iInf _).1 hx v
      have h2 := (Submodule.mem_iInf _).1 h1 hv
      exact LinearMap.mem_ker.1 h2
    have hβy : β (β⁻¹ x) = x := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    have hy : β⁻¹ x ∈ orth S (Xsp F) := by
      unfold orth
      rw [Submodule.mem_iInf]
      intro v
      rw [Submodule.mem_iInf]
      intro hv
      rw [LinearMap.mem_ker]
      have hv' : β v = v := fix_xsp hβ v hv
      rw [← hiso v (β⁻¹ x), hv', hβy]
      exact hxo v hv
    have hd := hX (β⁻¹ x) hy
    have hfix : β (n (β⁻¹ x) - β⁻¹ x) = n (β⁻¹ x) - β⁻¹ x := fix_xsp hβ _ hd
    have hc : (β * n * β⁻¹) x - x = β (n (β⁻¹ x) - β⁻¹ x) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, map_sub, hβy]
    rw [hc, hfix]
    exact hd

end NC

end Formalism.L2.SG.Pf.SatGramActL
