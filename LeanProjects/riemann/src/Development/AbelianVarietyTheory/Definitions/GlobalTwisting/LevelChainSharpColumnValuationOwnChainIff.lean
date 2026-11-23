import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalRingCardinality.DataKerP
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

structure Ch (D : D7) (u : D.what₂.Word) where
  C : ColumnChain D.R D.what₂.Tau (D.hcW u)
  A : ColumnsAtT D.R C
  P : PeriodMap D.R C
  fm : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P

abbrev own (D : D7) (u : D.what₂.Word) : Ch D u := ⟨(D.mem u).C, (D.mem u).A, (D.mem u).P, D.fm u⟩

abbrev tw {D : D7} (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Ch D u :=
  ⟨D.chTw u μ, Tw.A u μ, D.PTw u μ, Tw.fm u μ⟩

variable {D : D7} {u : D.what₂.Word} (X : Ch D u)

def duX : ℕ := haveI := X.A.Mu0_fd; Module.finrank ℂ X.A.Mu0

def TauWeight (τ : D.what₂.Tau) : ℕ :=
  (Finset.range (D.R.m + 1)).sup fun i => Finset.univ.sup fun a : Fin (D.R.N i) =>
    if a.1 = 0 ∧ τ ∈ topsOf D.host D.eTau then 0
    else ((X.fm.lam i τ).w a - ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)).natAbs

abbrev Fn (i : ℕ) : Type := X.C.cls i → X.C.Y i → ℂ

abbrev Vl (i : ℕ) : Type := (X.fm.lat i).V

instance lvModFin (i : ℕ) (v : X.A.vT) (c : X.C.cls i) :
    Module.Finite (X.A.Fv v) (X.fm.lv i v c) :=
  Module.finite_of_finrank_pos (by rw [X.fm.lv_rank]; exact D.R.N_pos i)

instance lvFintype (i : ℕ) (v : X.A.vT) (c : X.C.cls i) : Fintype (X.fm.lv i v c) :=
  haveI : Finite (X.fm.lv i v c) := Module.finite_of_finite (X.A.Fv v)
  Fintype.ofFinite _

def Uop (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => ∑ x ∈ Finset.univ.filter (fun x : X.fm.lv i v c => X.fm.fv i v c x = 1),
    (X.fm.upT i v c x).toLinearMap ∘ₗ LinearMap.proj (X.fm.up i v c x)

def VVT (w : D.what₂.places.Pl) : Finset X.A.vT :=
  if X.fm.seenP w then Finset.univ.filter (fun v => X.fm.tauOf w v ∈ topsOf D.host D.eTau) else ∅

def Uprod (i : ℕ) (w : D.what₂.places.Pl) : Fn X i →ₗ[ℂ] Fn X i :=
  (VVT X w).toList.foldr (fun v g => (Uop X i v).comp g) LinearMap.id

def imgL {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn X i →ₗ[ℂ] Fn X j)
    (A : Submodule (Ow D w) (Vl X i)) : Submodule (Ow D w) (Vl X j) where
  carrier := {y | ∃ x ∈ A, X.fm.emb j y = f (X.fm.emb i x)}
  add_mem' := by
    rintro a b ⟨x, hx, h1⟩ ⟨y, hy, h2⟩
    exact ⟨x + y, A.add_mem hx hy, by rw [map_add, map_add, map_add, h1, h2]⟩
  zero_mem' := ⟨0, A.zero_mem, by simp⟩
  smul_mem' := by
    rintro r a ⟨x, hx, h1⟩
    refine ⟨r • x, A.smul_mem r hx, ?_⟩
    rw [Subring.smul_def, Subring.smul_def, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h1,
      LinearMap.map_smul]

def Sram (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl X 0) :=
  X.fm.S 0 w ⊓ X.fm.ramSub.restrictScalars (Ow D w)

def expT (w : D.what₂.places.Pl) : ℤ :=
  (D.R.m : ℤ) * ∑ v ∈ VVT X w, X.fm.bTop (X.fm.tauOf w v)

def Nlam (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl X 0) :=
  imgL X w (((X.A.T : ℂ) ^ expT X w) • (Uprod X 0 w) ^ D.R.m) (Sram X w)

abbrev VV (w : D.what₂.places.Pl) : Finset X.A.vT := VVT X w

def OverT (w : D.what₂.places.Pl) : Prop := D.what₂.places.resChar w = X.A.T

def tpow (n : ℕ) : ℂ := (X.A.T : ℂ) ^ n

instance lkModFin (i : ℕ) (v : X.A.vT) (c : X.C.cls i) : Module.Finite (X.A.Fv v) (X.fm.lk i v c) :=
  Module.finite_of_finrank_pos (by rw [X.fm.lk_rank]; exact D.R.N_pos i)

instance lkDualFintype (i : ℕ) (v : X.A.vT) (c : X.C.cls i) :
    Fintype (Module.Dual (X.A.Fv v) (X.fm.lk i v c)) :=
  haveI : Finite (Module.Dual (X.A.Fv v) (X.fm.lk i v c)) := Module.finite_of_finite (X.A.Fv v)
  Fintype.ofFinite _

def Dop (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual (X.A.Fv v) (X.fm.lk i v c) => g (X.fm.te i v c) = 1),
    (X.fm.dnT i v c g).toLinearMap ∘ₗ LinearMap.proj (X.fm.dn i v c g)

def Eop (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual (X.A.Fv v) (X.fm.lk i v c) => g ≠ 0),
    (X.fm.dnT i v c g).toLinearMap ∘ₗ LinearMap.proj (X.fm.dn i v c g)

def dia (i : ℕ) (v : X.A.vT) (a : (X.A.Fv v)ˣ) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => (X.fm.dilT i v a c).toLinearMap ∘ₗ LinearMap.proj (X.fm.dil i v a c)

def Nm (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i := ∑ a : (X.A.Fv v)ˣ, dia X i v a

def trp (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  ((X.A.T : ℂ) ^ (D.R.N i - 1))⁻¹ • (Eop X i v ∘ₗ Uop X i v)

def FFop (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual (X.A.Fv v) (X.fm.lk i v c) => g ≠ 0),
    (X.A.psiT v (g (X.fm.te i v c))) • ((X.fm.dnT i v c g).toLinearMap ∘ₗ LinearMap.proj (X.fm.dn i v c g))

def Gs (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  ∑ a : (X.A.Fv v)ˣ, X.A.psiT v (a : X.A.Fv v) • dia X i v a

def GsD (i : ℕ) (v : X.A.vT) : Fn X i →ₗ[ℂ] Fn X i :=
  ∑ a : (X.A.Fv v)ˣ, X.A.psiT v (-(a : X.A.Fv v)) • dia X i v a⁻¹

theorem dia_zero (v : X.A.vT) (a : (X.A.Fv v)ˣ) : dia X 0 v a = X.A.rhoT v a := by
  apply LinearMap.ext; intro φ; funext c
  rw [X.fm.rhoT_dil v a φ c]; rfl

theorem Nm_zero (v : X.A.vT) : Nm X 0 v = X.A.Nm v := by
  unfold Nm ColumnsAtT.Nm; exact Finset.sum_congr rfl (fun a _ => dia_zero X v a)

theorem Gs_zero (v : X.A.vT) : Gs X 0 v = X.A.gauss v := by
  unfold Gs ColumnsAtT.gauss Formalism.ThetaLiftIndependence.gaussOp
  exact Finset.sum_congr rfl (fun a _ => by rw [dia_zero])

def MramI (i : ℕ) : Submodule ℂ (Fn X i) := X.fm.Fi i ⊓ ⨅ v, LinearMap.ker (Nm X i v)

theorem MramI_zero : MramI X 0 = X.A.Mram := by
  unfold MramI ColumnsAtT.Mram; rw [X.fm.Fi_zero]; simp only [Nm_zero]

def KT (i : ℕ) : Fn X i →ₗ[ℂ] Fn X (i + 1) := X.C.Klin i

def colT : Fn X 0 → Fn X D.R.m := X.C.col

theorem KT_apply (i : ℕ) (φ : Fn X i) : KT X i φ = X.C.K i φ := rfl

abbrev Wt (τ : D.what₂.Tau) : ℕ := TauWeight X τ

def amax : ℤ := (tops D).fold max 0 X.fm.aTop

def FFall (i : ℕ) : Fn X i →ₗ[ℂ] Fn X i :=
  (Finset.univ : Finset X.A.vT).toList.foldr (fun v g => (FFop X i v).comp g) LinearMap.id

def Into {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn X i → Fn X j)
    (A : Submodule (Ow D w) (Vl X i)) (B : Submodule (Ow D w) (Vl X j)) : Prop :=
  ∀ x ∈ A, ∃ y ∈ B, X.fm.emb j y = f (X.fm.emb i x)

def len {i : ℕ} (w : D.what₂.places.Pl) (A B : Submodule (Ow D w) (Vl X i)) : ℕ∞ :=
  Module.length (Ow D w) (A ⧸ B.comap A.subtype)

def tL {i : ℕ} (w : D.what₂.places.Pl) (n : ℤ) (A : Submodule (Ow D w) (Vl X i)) :
    Submodule (Ow D w) (Vl X i) :=
  imgL X w (((X.A.T : ℂ) ^ n) • LinearMap.id) A

def Alcove : Prop :=
  ∀ j, j ≤ D.R.m → ∀ τ (a b : Fin (D.R.N j)),
    2 * ((X.fm.lam j τ).w a - (X.fm.lam j τ).w b + (D.R.N j : ℤ)) < (X.A.T : ℤ)

def HidaSetting : Prop :=
  2 * D.R.f * D.R.N D.R.m + 1 < X.A.T ∧ (4 * amax X < (X.A.T : ℤ) ∧ Alcove X) ∧
    ∀ τ ∈ tops D, 0 ≤ X.fm.bTop τ

def UpDownIncidenceInverse : Prop := X.fm.DnUp ∧ X.fm.DnFv

def admS : Prop := X.C.StabZero

def RoundUp : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v c (x : X.fm.lv i v c), X.fm.fv i v c x = 1 →
    ∃ e : X.fm.lk i v (X.fm.up i v c x) ≃ₗ[X.A.Fv v] X.fm.lv i v c,
      e (X.fm.te i v (X.fm.up i v c x)) = x ∧
      X.fm.dn i v (X.fm.up i v c x) ((X.fm.fv i v c).comp e.toLinearMap) = c ∧
      ∀ φ ∈ X.fm.Fi i,
        X.fm.upT i v c x (X.fm.dnT i v (X.fm.up i v c x) ((X.fm.fv i v c).comp e.toLinearMap)
          (φ (X.fm.dn i v (X.fm.up i v c x) ((X.fm.fv i v c).comp e.toLinearMap)))) = φ c

def RoundDn : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v c (g : Module.Dual (X.A.Fv v) (X.fm.lk i v c)), g (X.fm.te i v c) = 1 →
    ∃ e : X.fm.lv i v (X.fm.dn i v c g) ≃ₗ[X.A.Fv v] X.fm.lk i v c,
      X.fm.fv i v (X.fm.dn i v c g) = g.comp e.toLinearMap ∧
      X.fm.up i v (X.fm.dn i v c g) (e.symm (X.fm.te i v c)) = c ∧
      ∀ φ ∈ X.fm.Fi i,
        X.fm.dnT i v c g (X.fm.upT i v (X.fm.dn i v c g) (e.symm (X.fm.te i v c))
          (φ (X.fm.up i v (X.fm.dn i v c g) (e.symm (X.fm.te i v c))))) = φ c

def TrIso : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v c, ∀ φ ∈ X.fm.Fi i, ∀ ψ ∈ X.fm.Fi i,
    (∀ x : X.fm.lv i v c, X.fm.fv i v c x = 1 →
      X.fm.ipV i c (X.fm.upT i v c x (φ (X.fm.up i v c x))) (X.fm.upT i v c x (ψ (X.fm.up i v c x))) =
        X.fm.ipV i (X.fm.up i v c x) (φ (X.fm.up i v c x)) (ψ (X.fm.up i v c x))) ∧
    (∀ g : Module.Dual (X.A.Fv v) (X.fm.lk i v c), g ≠ 0 →
      X.fm.ipV i c (X.fm.dnT i v c g (φ (X.fm.dn i v c g))) (X.fm.dnT i v c g (ψ (X.fm.dn i v c g))) =
        X.fm.ipV i (X.fm.dn i v c g) (φ (X.fm.dn i v c g)) (ψ (X.fm.dn i v c g))) ∧
    ∀ a : (X.A.Fv v)ˣ,
      X.fm.ipV i c (X.fm.dilT i v a c (φ (X.fm.dil i v a c))) (X.fm.dilT i v a c (ψ (X.fm.dil i v a c))) =
        X.fm.ipV i (X.fm.dil i v a c) (φ (X.fm.dil i v a c)) (ψ (X.fm.dil i v a c))

def DiaMul : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ X.fm.Fi i,
    dia X i v 1 φ = φ ∧ ∀ a b, dia X i v (a * b) φ = dia X i v a (dia X i v b φ)

def admT : Prop := RoundUp X ∧ RoundDn X ∧ TrIso X ∧ DiaMul X

def Conclusion1 : Prop :=
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ X.fm.Fi i,
    Uop X i v φ ∈ X.fm.Fi i ∧ Dop X i v φ ∈ X.fm.Fi i ∧ ∀ a, dia X i v a φ ∈ X.fm.Fi i) ∧
  (∀ i, i ≤ D.R.m → ∀ v v', v ≠ v' → ∀ φ ∈ X.fm.Fi i,
    Uop X i v (Uop X i v' φ) = Uop X i v' (Uop X i v φ)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ X.fm.Fi i, ∀ ψ ∈ X.fm.Fi i,
    X.fm.ipC i (Uop X i v φ) ψ = X.fm.ipC i φ (Dop X i v ψ)) ∧
  (∀ i, i ≤ D.R.m → ∀ w, OverT X w → X.fm.seenP w = true → ∀ v,
    Into X w (Uop X i v) (X.fm.Bw i w v) (X.fm.S i w) ∧
    Into X w (Dop X i v) (X.fm.S i w) (X.fm.Bw i w v)) ∧
  (∀ i, i ≤ D.R.m → ∀ w, ¬ OverT X w → ∀ v,
    Into X w (Uop X i v) (X.fm.S i w) (X.fm.S i w) ∧ Into X w (Dop X i v) (X.fm.S i w) (X.fm.S i w)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ X.fm.Fi i, Dop X i v (Uop X i v φ) =
    (X.A.T : ℂ) ^ (D.R.N i - 1) • φ - (X.A.T : ℂ) ^ (D.R.N i - 2) • Nm X i v φ
      + (X.A.T : ℂ) ^ (D.R.N i - 2) • trp X i v φ) ∧
  (∀ v, ∀ x ∈ X.fm.ramSub,
    (∃ y ∈ X.fm.ramSub, X.fm.emb 0 y = Uop X 0 v (X.fm.emb 0 x)) ∧
    (∃ y ∈ X.fm.ramSub, X.fm.emb 0 y = Dop X 0 v (X.fm.emb 0 x)) ∧
    ∀ a, ∃ y ∈ X.fm.ramSub, X.fm.emb 0 y = dia X 0 v a (X.fm.emb 0 x)) ∧
  (∀ w, ¬ OverT X w → ∀ v,
    Into X w (Uop X 0 v) (Sram X w) (Sram X w) ∧
    Into X w (Dop X 0 v) (Sram X w) (Sram X w) ∧
    ∀ a, Into X w (dia X 0 v a) (Sram X w) (Sram X w)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI X i,
    Uop X i v φ ∈ MramI X i ∧ Dop X i v φ ∈ MramI X i ∧
    (∀ a, dia X i v a φ ∈ MramI X i) ∧ trp X i v φ = 0 ∧
    Dop X i v (Uop X i v φ) = (X.A.T : ℂ) ^ (D.R.N i - 1) • φ ∧
    Uop X i v (Dop X i v φ) = (X.A.T : ℂ) ^ (D.R.N i - 1) • φ)

def Conclusion2 : Prop :=
  (X.A.du : ℚ) = (duX X : ℚ) * (1 - 1 / ((X.A.T : ℚ) - 1)) ^ D.R.f ∧
  X.fm.ramLat.mu = (X.fm.lat 0).mu -
    (D.R.f : ℝ) * Real.log ((X.A.T : ℝ) - 1) / ((X.A.T : ℝ) - 2) ∧
  X.fm.ramLat.muMax ≤ (X.fm.lat 0).muMax ∧
  (∀ w, OverT X w → X.fm.seenP w = true → ∀ v,
    (0 ≤ (X.fm.lam 0 (X.fm.tauOf w v)).detShift →
      X.fm.S 0 w ≤ X.fm.Bw 0 w v ∧
      (∃ n : ℕ, len X w (X.fm.Bw 0 w v) (X.fm.S 0 w) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
          ((duX X : ℚ) * (wsum (X.fm.lam 0 (X.fm.tauOf w v)) : ℚ) / (D.R.k : ℚ))) ∧
      len X w (Sram X w) (imgL X w (Uop X 0 v) (Sram X w)) ≤
        len X w (X.fm.Bw 0 w v) (X.fm.S 0 w) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * duX X) : ℕ) : ℕ∞) +
          len X w (imgL X w (Uop X 0 v) (Sram X w)) (Sram X w)) ∧
    (0 ≤ X.fm.bTop (X.fm.tauOf w v) →
      tL X w (X.fm.bTop (X.fm.tauOf w v)) (X.fm.S 0 w) ≤ X.fm.Bw 0 w v ∧
      (∃ n : ℕ, len X w (X.fm.Bw 0 w v) (tL X w (X.fm.bTop (X.fm.tauOf w v)) (X.fm.S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((duX X : ℚ) *
          ((wsum (X.fm.lam 0 (X.fm.tauOf w v)) : ℚ) + (D.R.k : ℚ) * (X.fm.bTop (X.fm.tauOf w v) : ℚ)) /
            (D.R.k : ℚ))) ∧
      len X w (Sram X w)
          (imgL X w (((X.A.T : ℂ) ^ X.fm.bTop (X.fm.tauOf w v)) • Uop X 0 v) (Sram X w)) ≤
        len X w (X.fm.Bw 0 w v) (tL X w (X.fm.bTop (X.fm.tauOf w v)) (X.fm.S 0 w)) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * duX X) : ℕ) : ℕ∞) +
          len X w (imgL X w (((X.A.T : ℂ) ^ X.fm.bTop (X.fm.tauOf w v)) • Uop X 0 v) (Sram X w))
            (Sram X w)))

def IsBfam (i : ℕ) (w : D.what₂.places.Pl)
    (BV : Finset X.A.vT → Submodule (Ow D w) (Vl X i)) : Prop :=
  BV ∅ = X.fm.S i w ∧ (∀ v, BV {v} = X.fm.Bw i w v) ∧
  (∀ V v, v ∈ V → Into X w (Uop X i v) (BV V) (BV (V.erase v)) ∧
    Into X w (Dop X i v) (BV (V.erase v)) (BV V)) ∧
  (∀ V v, v ∈ V → X.fm.tauOf w v ∉ tops D →
    Into X w (fun φ => tpow X (2 * Wt X (X.fm.tauOf w v) + D.R.t) • φ) (BV V) (BV (V.erase v)))

def lossK (C : ℝ) : ℕ := ⌊∑ τ, (2 * (Wt X τ : ℝ) + C * D.R.N D.R.m)⌋₊

def PointsLemma (C : ℝ) : Prop :=
  ∀ w, OverT X w →
    (∀ i, i < D.R.m →
      (X.fm.seenP w = false →
        Into X w (fun φ => tpow X (lossK X C) • KT X i φ) (X.fm.S i w) (X.fm.S (i + 1) w)) ∧
      (X.fm.seenP w = true → ∃ BV, IsBfam X (i + 1) w BV ∧
        Into X w (fun φ => tpow X (lossK X C) • KT X i φ) (X.fm.S i w) (BV Finset.univ)) ∧
      (∃ e1 : ℕ, (e1 : ℝ) ≤ 4 * ∑ τ, (Wt X τ : ℝ) + C * D.R.f * D.R.N D.R.m ∧
        Into X w (fun φ => tpow X e1 • Uprod X (i + 1) w (KT X i φ))
          (X.fm.S i w) (X.fm.S (i + 1) w))) ∧
    (∀ i, i ≤ D.R.m → X.fm.seenP w = true → ∀ v, X.fm.tauOf w v ∉ tops D →
      Into X w (fun φ => tpow X (2 * Wt X (X.fm.tauOf w v) + D.R.t) • φ) (X.fm.Bw i w v) (X.fm.S i w))

def T4with (bd : D.what₂.places.Pl → X.A.vT → ℝ) : Prop :=
  ∀ i, i < D.R.m → ∀ v : X.A.vT,
    (∃ c : D.what₂.LL,
      (∀ φ ∈ X.fm.Fi i, Uop X (i + 1) v (KT X i φ) =
        D.what₂.embLL c • KT X i (Uop X i v φ)) ∧
      (∀ σ : D.what₂.LL →+* ℂ, ‖σ c‖ = (X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2)) ∧
      (∀ w, OverT X w → ∃ n : ℤ, D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) ∧
        |(n : ℝ)| ≤ (D.what₂.places.ramIdx w : ℝ) * bd w v)) ∧
    (∀ a, ∀ φ ∈ X.fm.Fi i, KT X i (dia X i v a φ) = dia X (i + 1) v a (KT X i φ)) ∧
    ∀ φ ∈ MramI X i, KT X i φ ∈ MramI X (i + 1)

def Conclusion4 (C : ℝ) : Prop :=
  T4with X (fun w v => (D.R.t : ℝ) + 1 + 2 * Wt X (X.fm.tauOf w v) + C * D.R.N D.R.m)

def LevelChainUOperatorCommutation : Prop :=
  ∀ i, i < D.R.m → ∀ v : X.A.vT, ∀ φ ∈ X.fm.Fi i,
    Uop X (i + 1) v (KT X i φ) =
      ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) • KT X i (Uop X i v φ)

def Conclusion5 (C : ℝ) : Prop :=
  ∀ w, OverT X w →
    Nlam X w ≤ Sram X w ∧
    (∃ e : ℕ, (e : ℝ) ≤ D.R.m * (4 * ∑ τ, (Wt X τ : ℝ) + C * D.R.f * D.R.N D.R.m) +
        ∑ v ∈ VV X w, ((D.R.t : ℝ) + 1 + 2 * Wt X (X.fm.tauOf w v) + C * D.R.N D.R.m) *
          ((D.R.m : ℝ) * (D.R.m + 1) / 2) ∧
      Into X w (fun φ => tpow X e • colT X φ) (Nlam X w) (X.fm.S D.R.m w)) ∧
    (∃ n : ℕ, len X w (Sram X w) (Nlam X w) = n ∧
      (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * duX X * ∑ v ∈ VV X w,
        ((amax X : ℝ) / D.R.k + 2 * Wt X (X.fm.tauOf w v) + D.R.k + X.fm.bTop (X.fm.tauOf w v))))

def ETpi : ℝ :=
  2 * ∑ τ, (Wt X τ : ℝ) + (D.R.f : ℝ) * D.R.N D.R.m +
    ((tops D).card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4

def ET (w : D.what₂.places.Pl) : ℝ := if X.fm.seenP w then ETpi X else 0

def Conclusion5Sharp : Prop :=
  ∀ w, OverT X w → ∀ (c : D.what₂.LL) (n : ℤ), D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) →
    (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * ET X w) ≤ (n : ℝ) →
    Into X w (fun φ => D.what₂.embLL c • colT X φ) (Nlam X w) (X.fm.S D.R.m w)

def WeightBudgetBound (L : SizeData₂ D) (C : ℝ) : Prop :=
  (∀ S : Finset D.what₂.places.Pl, (∀ w ∈ S, OverT X w) →
    0 ≤ ∑ w ∈ S, SizeData₂.sz w (ET X w) ∧
    ∑ w ∈ S, SizeData₂.sz w (ET X w) ≤ ETpi X * Real.log (X.A.T : ℝ)) ∧
  ETpi X * Real.log (X.A.T : ℝ) ≤ C * L.B0

def Pt : Fn X D.R.m →ₗ[ℂ] X.P.Wrow := X.P.lowerMap ∘ₗ X.P.evz

def ptB : ℝ := ∏ τ, (X.A.T : ℝ) ^ (-(X.fm.deg τ)) * X.fm.beOn τ ^ 2

def Conclusion6 : Prop :=
  Function.Injective X.fm.til ∧
  (∀ c, Function.Bijective (X.fm.stabMap c)) ∧
  (∀ φ ∈ X.fm.Fi D.R.m, Pt X φ ∈ X.fm.ptC) ∧
  (∃ h : X.fm.PRat, X.fm.PtilIntegral h ∧
    ∀ (v : InfinitePlace D.what₂.LL) (x : Vl X D.R.m),
      (Formalism.HermitianLatticesTheory.majAt X.fm.ptLat.b X.fm.ptLat.X v (X.fm.PtL h x) (X.fm.PtL h x)).re ≤
        ptB X * (Formalism.HermitianLatticesTheory.majAt (X.fm.lat D.R.m).b (X.fm.lat D.R.m).X v x x).re) ∧
  ∀ φ ∈ X.fm.Fi D.R.m, (X.fm.ipP (Pt X φ) (Pt X φ)).re ≤ ptB X * (X.fm.ipC D.R.m φ φ).re

def division_rows_rational_lattice : Prop :=
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI X i, FFop X i v φ = Dop X i v (Gs X i v φ)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ X.fm.Fi i,
    Gs X i v (GsD X i v φ) = (X.A.T : ℂ) • φ - Nm X i v φ) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI X i, FFop X i v φ ∈ MramI X i) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI X i, ∀ ψ ∈ MramI X i,
    X.fm.ipC i (FFop X i v φ) (FFop X i v ψ) = (X.A.T : ℂ) ^ D.R.N i * X.fm.ipC i φ ψ) ∧
  (∀ i, i ≤ D.R.m → ∀ φ ∈ MramI X i, ∀ ψ ∈ MramI X i,
    X.fm.ipC i (FFall X i φ) (FFall X i ψ) = (X.A.T : ℂ) ^ (D.R.f * D.R.N i) * X.fm.ipC i φ ψ) ∧
  (∀ i, i < D.R.m → ∀ v, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ MramI X i,
    FFop X (i + 1) v (KT X i φ) = c • KT X i (FFop X i v φ))

def lamTr (τ : D.what₂.Tau) : DomWeight (D.R.N D.R.m) := wSh (X.fm.lam D.R.m τ) (cTw D.R)

def sgTr (τ : D.what₂.Tau) : DomWeight (D.R.N D.R.m - 1) := wSh (X.fm.sg τ) (cTw D.R)

theorem interlaceTr (h : X.fm.SgInterlace) (τ : D.what₂.Tau) :
    Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr X τ) (sgTr X τ) :=
  fun i => ⟨sub_le_sub_right (h τ i).1 _, sub_le_sub_right (h τ i).2 _⟩

def sqrtT : ℂˣ := Units.mk0 ((Real.sqrt (X.A.T : ℝ) : ℝ) : ℂ) (by
  have h : 0 < (X.A.T : ℝ) := by exact_mod_cast X.A.T_prime.pos
  exact_mod_cast (Real.sqrt_pos.mpr h).ne')

def gFull (g : GL (Fin (D.R.N D.R.m - 1)) ℂ) : GL (Fin (D.R.N D.R.m)) ℂ :=
  Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) g * Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ _ (sqrtT X)

def opNorm (τ : D.what₂.Tau) (b : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) : ℝ :=
  sSup ((fun f => Real.sqrt ((normFock (X.fm.sg τ) (b f) (b f)).re /
      (normFock (X.fm.lam D.R.m τ) f f).re)) '' {f | f ∈ delSq ℂ _ (X.fm.lam D.R.m τ) ∧ f ≠ 0})

def TupleChainSharpColumnValuation (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ w, Formalism.MainNotions.product_first_zeroth_parts.OverT D u w → ∀ (c : D.what₂.LL) (n : ℤ), D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) →
    (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * EatT D u w) ≤ (n : ℝ) →
    ∀ x ∈ LT.Nlam D u w, ∃ y ∈ (Tw.fm u μ).S D.R.m w,
      (Tw.fm u μ).emb D.R.m y = D.what₂.embLL c • (D.chTw u μ).col (D.e0Tw u μ ((D.fm u).emb 0 x))

def EveryLevelLiftProperties : Prop :=
  Function.Injective X.fm.til ∧
  (∀ c, Function.Bijective (X.fm.stabMap c)) ∧
  (∀ φ ∈ X.fm.Fi D.R.m, Pt X φ ∈ X.fm.ptC) ∧
  ∃ h : X.fm.PRat, X.fm.PtilIntegral h

theorem everyLevelPart_of_full (h : Conclusion6 X) : EveryLevelLiftProperties X :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.elim fun hP hh => ⟨hP, hh.1⟩⟩

def BaseDet (cl : letI := D.host.cmStar; ∀ i, X.C.cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V)
    (dt : ∀ i, X.C.cls i → D.Dt) : Prop :=
  letI := D.host.cmStar
  ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = (X.A.T : D.host.E) ∧
    (∀ w, OverT X w → (X.fm.seenP w = true ↔ 0 < D.what₂.places.val w (D.embE (π : D.host.E)))) ∧
    ∀ i, i ≤ D.R.m →
      ∃ (co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) (L0 : SDLat D.host.E (D.R.N i)),
        (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
        (∀ y, co y ∈ L0.1 ↔ y ∈ (D.sp.X i).L0) ∧
        ∀ c : X.C.cls i, ∃ Ln : SDLat D.host.E (D.R.N i),
          (∀ y, co y ∈ Ln.1 ↔ ∃ a ∈ cl i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (cl i c),
            y = a + D.host.conj (π : D.host.E) • b) ∧
          (QuotientGroup.mk (dt i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) L0 Ln

def admB (cl : letI := D.host.cmStar; ∀ i, X.C.cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V)
    (mt : ℕ → D.Dt →* ℂˣ) (dt : ∀ i, X.C.cls i → D.Dt) : Prop :=
  (letI := D.host.cmStar; ∀ i c, Submodule.IsLattice D.host.E (cl i c)) ∧
    Formalism.MainNotions.GL3Theta.CarriesTupleCharacters D X.C mt dt ∧ BaseDet X cl dt

def NatComp (cl : letI := D.host.cmStar; ∀ i, X.C.cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V)
    (O : Formalism.MainNotions.GL3Theta.LiftObj D X.C) : Prop :=
  letI := D.host.cmStar
  ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = (X.A.T : D.host.E) ∧
    (∀ w, OverT X w → (X.fm.seenP w = true ↔ 0 < D.what₂.places.val w (D.embE (π : D.host.E)))) ∧
    ∀ i, i ≤ D.R.m → ∃ co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E),
      (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
      (∀ y, co y ∈ (O.L0 i).1 ↔ y ∈ (D.sp.X i).L0) ∧
      ∀ (c : X.C.cls i) y, co y ∈ (O.lat i c).1 ↔
        ∃ a ∈ cl i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (cl i c), y = a + D.host.conj (π : D.host.E) • b

theorem admissibleBasis_of_naturalComparison (cl : letI := D.host.cmStar; ∀ i, X.C.cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V)
    (hcl : letI := D.host.cmStar; ∀ i c, Submodule.IsLattice D.host.E (cl i c))
    (O : Formalism.MainNotions.GL3Theta.LiftObj D X.C) (h : NatComp X cl O) : admB X cl O.mt O.dt := by
  obtain ⟨π, h1, h2, h3, h4⟩ := h
  refine ⟨hcl, O.c13, π, h1, h2, h3, fun i hi => ?_⟩
  obtain ⟨co, a, b, c⟩ := h4 i hi
  exact ⟨co, O.L0 i, a, b, fun d => ⟨O.lat i d, c d, O.dt_lat i d⟩⟩

section Indep

variable (Y : Ch D u)

theorem lam_indep (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) (a : Fin (D.R.N j)) :
    (X.fm.lam j τ).w a = (Y.fm.lam j τ).w a := by
  have h := (X.fm.lam_eq j hj τ a).trans (Y.fm.lam_eq j hj τ a).symm
  exact_mod_cast h

theorem Wt_indep (τ : D.what₂.Tau) : Wt X τ = Wt Y τ := by
  unfold Wt TauWeight
  refine Finset.sup_congr rfl fun i hi => Finset.sup_congr rfl fun a _ => ?_
  rw [lam_indep X Y i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) τ a]

theorem ETpi_indep : ETpi X = ETpi Y := by
  unfold ETpi; simp only [Wt_indep X Y]

theorem aTop_indep : X.fm.aTop = Y.fm.aTop :=
  funext fun τ => lam_indep X Y 0 (Nat.zero_le _) τ _

theorem bTop_indep : X.fm.bTop = Y.fm.bTop := by
  funext τ
  unfold MemberForms.bTop DomWeight.detShift
  rw [dif_pos (D.R.N_pos 0), dif_pos (D.R.N_pos 0), lam_indep X Y 0 (Nat.zero_le _)]

theorem levelSetting_indep_chain (hT : X.A.T = Y.A.T) : HidaSetting X ↔ HidaSetting Y := by
  have hA : Alcove X ↔ Alcove Y := by
    unfold Alcove
    refine forall_congr' fun j => forall_congr' fun hj => forall_congr' fun τ => forall_congr' fun a =>
      forall_congr' fun b => ?_
    rw [lam_indep X Y j hj τ a, lam_indep X Y j hj τ b, hT]
  unfold HidaSetting amax
  rw [hA, hT, aTop_indep X Y, bTop_indep X Y]

end Indep

theorem emb_mem_Fi (i : ℕ) (x : Vl X i) : X.fm.emb i x ∈ X.fm.Fi i := by
  rw [← (X.fm.emb_basis i).2, ← (X.fm.lat i).b.sum_repr x, map_sum]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

def UComm : Prop :=
  (∀ v, ∀ φ ∈ X.fm.Fi 0, Uop X 0 v φ ∈ X.fm.Fi 0) ∧
  ∀ v v', v ≠ v' → ∀ φ ∈ X.fm.Fi 0, Uop X 0 v (Uop X 0 v' φ) = Uop X 0 v' (Uop X 0 v φ)

theorem upCommute_of_firstProperty (h : Conclusion1 X) : UComm X :=
  ⟨fun v φ hφ => (h.1 0 (Nat.zero_le _) v φ hφ).1, h.2.1 0 (Nat.zero_le _)⟩

def Ulist (l : List X.A.vT) : Fn X 0 →ₗ[ℂ] Fn X 0 := l.foldr (fun v g => (Uop X 0 v).comp g) LinearMap.id

variable {X}

theorem Ulist_mem (h : UComm X) (l : List X.A.vT) {φ : Fn X 0} (hφ : φ ∈ X.fm.Fi 0) : Ulist X l φ ∈ X.fm.Fi 0 := by
  induction l with
  | nil => exact hφ
  | cons v l ih => exact h.1 v _ ih

theorem Ulist_perm (h : UComm X) {l l' : List X.A.vT} (p : l.Perm l') {φ : Fn X 0} (hφ : φ ∈ X.fm.Fi 0) :
    Ulist X l φ = Ulist X l' φ := by
  induction p with
  | nil => rfl
  | cons v _ ih => exact congrArg (Uop X 0 v) ih
  | swap v v' l =>
    by_cases hv : v' = v
    · subst hv; rfl
    · exact h.2 v' v hv _ (Ulist_mem h l hφ)
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

structure SharedBy (X Y : Ch D u) (e : Fn X 0 ≃ₗ[ℂ] Fn Y 0) (eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0)
    (ev : X.A.vT ≃ Y.A.vT) (eF : ∀ v, X.A.Fv v ≃+* Y.A.Fv (ev v)) : Prop where
  T_eq : Y.A.T = X.A.T
  emb_eq : ∀ x, Y.fm.emb 0 (eL x) = e (X.fm.emb 0 x)
  lat_iff : ∀ x, x ∈ (X.fm.lat 0).L ↔ eL x ∈ (Y.fm.lat 0).L
  ip_eq : ∀ φ ∈ X.fm.Fi 0, ∀ ψ ∈ X.fm.Fi 0, Y.fm.ipC 0 (e φ) (e ψ) = X.fm.ipC 0 φ ψ
  psi_eq : ∀ v a, Y.A.psiT (ev v) (eF v a) = X.A.psiT v a
  seen_eq : ∀ w, OverT X w → Y.fm.seenP w = X.fm.seenP w
  tau_eq : ∀ w, OverT X w → ∀ v, Y.fm.tauOf w (ev v) = X.fm.tauOf w v
  B_iff : ∀ w, OverT X w → X.fm.seenP w = true → ∀ v x, x ∈ X.fm.Bw 0 w v ↔ eL x ∈ Y.fm.Bw 0 w (ev v)
  U_eq : ∀ v, ∀ φ ∈ X.fm.Fi 0, e (Uop X 0 v φ) = Uop Y 0 (ev v) (e φ)
  D_eq : ∀ v, ∀ φ ∈ X.fm.Fi 0, e (Dop X 0 v φ) = Dop Y 0 (ev v) (e φ)
  dia_eq : ∀ v (a : (X.A.Fv v)ˣ), ∀ φ ∈ X.fm.Fi 0,
    e (dia X 0 v a φ) = dia Y 0 (ev v) (Units.map (eF v : X.A.Fv v →* Y.A.Fv (ev v)) a) (e φ)

def Shared (X Y : Ch D u) (e : Fn X 0 ≃ₗ[ℂ] Fn Y 0) (eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0) : Prop :=
  ∃ (ev : X.A.vT ≃ Y.A.vT) (eF : ∀ v, X.A.Fv v ≃+* Y.A.Fv (ev v)), SharedBy X Y e eL ev eF

theorem SharedBy.refl (X : Ch D u) : SharedBy X X (LinearEquiv.refl ℂ _) (LinearEquiv.refl _ _) (Equiv.refl _)
    (fun _ => RingEquiv.refl _) :=
  ⟨rfl, fun _ => rfl, fun _ => Iff.rfl, fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ _ _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem Shared.refl (X : Ch D u) : Shared X X (LinearEquiv.refl ℂ _) (LinearEquiv.refl _ _) :=
  ⟨_, _, SharedBy.refl X⟩

theorem Shared.of_eq {X Y : Ch D u} (h : Y = X) (e : Fn X 0 ≃ₗ[ℂ] Fn Y 0) (eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0)
    (he : ∀ φ, HEq (e φ) φ) (hL : ∀ x, Y.fm.emb 0 (eL x) = e (X.fm.emb 0 x)) : Shared X Y e eL := by
  subst h
  obtain rfl : e = LinearEquiv.refl ℂ _ := LinearEquiv.ext fun φ => eq_of_heq (he φ)
  obtain rfl : eL = LinearEquiv.refl _ _ := LinearEquiv.ext fun x => Y.fm.emb_inj 0 (hL x)
  exact Shared.refl Y

namespace SharedBy

variable {Y : Ch D u} {e : Fn X 0 ≃ₗ[ℂ] Fn Y 0} {eL : Vl X 0 ≃ₗ[D.what₂.LL] Vl Y 0}
  {ev : X.A.vT ≃ Y.A.vT} {eF : ∀ v, X.A.Fv v ≃+* Y.A.Fv (ev v)} (h : SharedBy X Y e eL ev eF)
include h

theorem overT_iff (w : D.what₂.places.Pl) : OverT Y w ↔ OverT X w := by
  unfold OverT; rw [h.T_eq]

theorem S_iff (w : D.what₂.places.Pl) (x : Vl X 0) : eL x ∈ Y.fm.S 0 w ↔ x ∈ X.fm.S 0 w := by
  constructor
  · intro hx
    have key : ∀ y ∈ Y.fm.S 0 w, eL.symm y ∈ X.fm.S 0 w := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem z hz => exact Submodule.subset_span ((h.lat_iff _).mpr (by rw [eL.apply_symm_apply]; exact hz))
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
      | smul r a _ ha =>
        rw [Subring.smul_def, map_smul]
        exact Submodule.smul_mem _ r ha
    simpa using key _ hx
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span ((h.lat_iff z).mp hz)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Subring.smul_def, map_smul]
      exact Submodule.smul_mem _ r ha

theorem Nm_eq (v : X.A.vT) {φ : Fn X 0} (hφ : φ ∈ X.fm.Fi 0) : e (Nm X 0 v φ) = Nm Y 0 (ev v) (e φ) := by
  unfold Nm
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Fintype.sum_equiv (Units.mapEquiv (eF v).toMulEquiv).toEquiv _ _ fun a => h.dia_eq v a φ hφ

theorem ramSub_iff (x : Vl X 0) : eL x ∈ Y.fm.ramSub ↔ x ∈ X.fm.ramSub := by
  show Y.fm.emb 0 (eL x) ∈ Y.A.Mram ↔ X.fm.emb 0 x ∈ X.A.Mram
  rw [← MramI_zero X, ← MramI_zero Y]
  unfold MramI
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, emb_mem_Fi, true_and]
  rw [h.emb_eq, ← ev.forall_congr_right]
  refine forall_congr' fun v => ?_
  rw [← h.Nm_eq v (emb_mem_Fi X 0 x), e.map_eq_zero_iff]

theorem Sram_iff (w : D.what₂.places.Pl) (x : Vl X 0) : eL x ∈ Sram Y w ↔ x ∈ Sram X w :=
  and_congr (h.S_iff w x) (h.ramSub_iff x)

theorem VVT_eq {w : D.what₂.places.Pl} (hw : OverT X w) : VVT Y w = (VVT X w).map ev.toEmbedding := by
  unfold VVT
  rw [h.seen_eq w hw]
  split_ifs
  · ext y
    obtain ⟨v, rfl⟩ := ev.surjective y
    simp [h.tau_eq w hw]
  · rfl

theorem expT_eq {w : D.what₂.places.Pl} (hw : OverT X w) : expT Y w = expT X w := by
  unfold expT
  rw [h.VVT_eq hw, Finset.sum_map, bTop_indep Y X]
  simp only [Equiv.coe_toEmbedding, h.tau_eq w hw]

theorem ET_eq {w : D.what₂.places.Pl} (hw : OverT X w) : ET Y w = ET X w := by
  unfold ET; rw [h.seen_eq w hw, ETpi_indep Y X]

theorem Ulist_eq (hU : UComm X) (l : List X.A.vT) {φ : Fn X 0} (hφ : φ ∈ X.fm.Fi 0) :
    e (Ulist X l φ) = Ulist Y (l.map ev) (e φ) := by
  induction l with
  | nil => rfl
  | cons v l ih => exact (h.U_eq v _ (Ulist_mem hU l hφ)).trans (congrArg (Uop Y 0 (ev v)) ih)

theorem Uprod_eq (hU : UComm X) {w : D.what₂.places.Pl} (hw : OverT X w) {φ : Fn X 0} (hφ : φ ∈ X.fm.Fi 0) :
    e (Uprod X 0 w φ) = Uprod Y 0 w (e φ) := by
  have p : (VVT X w).toList.Perm ((VVT Y w).toList.map ev.symm) := by
    rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Finset.coe_toList, Finset.coe_toList, h.VVT_eq hw]
    simp [Multiset.map_map]
  show e (Ulist X _ φ) = Ulist Y _ (e φ)
  rw [Ulist_perm hU p hφ, h.Ulist_eq hU _ hφ, List.map_map]
  simp

theorem Uprod_pow_eq (hU : UComm X) {w : D.what₂.places.Pl} (hw : OverT X w) (n : ℕ) {φ : Fn X 0}
    (hφ : φ ∈ X.fm.Fi 0) : e ((Uprod X 0 w ^ n) φ) = (Uprod Y 0 w ^ n) (e φ) := by
  induction n generalizing φ with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← h.Uprod_eq hU hw hφ]
    exact ih (Ulist_mem hU _ hφ)

theorem Nlam_iff (hU : UComm X) {w : D.what₂.places.Pl} (hw : OverT X w) (x : Vl X 0) :
    eL x ∈ Nlam Y w ↔ x ∈ Nlam X w := by
  have key : ∀ z : Vl X 0, Y.fm.emb 0 (eL x) = (((Y.A.T : ℂ) ^ expT Y w) • (Uprod Y 0 w) ^ D.R.m) (Y.fm.emb 0 (eL z)) ↔
      X.fm.emb 0 x = (((X.A.T : ℂ) ^ expT X w) • (Uprod X 0 w) ^ D.R.m) (X.fm.emb 0 z) := by
    intro z
    rw [h.emb_eq, h.emb_eq, LinearMap.smul_apply, LinearMap.smul_apply, ← h.Uprod_pow_eq hU hw _ (emb_mem_Fi X 0 z),
      h.T_eq, h.expT_eq hw, ← map_smul, e.injective.eq_iff]
  constructor
  · rintro ⟨y, hy, hh⟩
    obtain ⟨z, rfl⟩ := eL.surjective y
    exact ⟨z, (h.Sram_iff w z).mp hy, (key z).mp hh⟩
  · rintro ⟨z, hz, hh⟩
    exact ⟨eL z, (h.Sram_iff w z).mpr hz, (key z).mpr hh⟩

end SharedBy

def TwTie (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  Shared (own D u) (tw Tw u μ) (D.e0Tw u μ) (Tw.e0 u μ)

theorem TwTie.of_copy (Tw : TwForms D) (μ : D.what₂.Tup) (h : tw Tw u μ = own D u)
    (he : ∀ φ, HEq (D.e0Tw u μ φ) φ) : TwTie Tw u μ :=
  Shared.of_eq h _ _ he (Tw.embed_mul_block_embedding u μ)

theorem Wt_tw (Tw : TwForms D) (μ : D.what₂.Tup) (τ : D.what₂.Tau) : Wt (tw Tw u μ) τ = Wtau D u τ :=
  Wt_indep (tw Tw u μ) (own D u) τ

theorem levelSetting_twist_iff (Tw : TwForms D) (μ : D.what₂.Tup) : HidaSetting (tw Tw u μ) ↔ Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u :=
  levelSetting_indep_chain (tw Tw u μ) (own D u) (Tw.A_T u μ)

theorem OverT_tw (Tw : TwForms D) (μ : D.what₂.Tup) (w : D.what₂.places.Pl) :
    OverT (tw Tw u μ) w ↔ Formalism.MainNotions.product_first_zeroth_parts.OverT D u w := by
  show D.what₂.places.resChar w = (Tw.A u μ).T ↔ _
  rw [Tw.A_T]; rfl

theorem TwTie.ET_eq {Tw : TwForms D} {μ : D.what₂.Tup} (h : TwTie Tw u μ) {w : D.what₂.places.Pl}
    (hw : Formalism.MainNotions.product_first_zeroth_parts.OverT D u w) : ET (tw Tw u μ) w = EatT D u w :=
  h.elim fun _ h => h.elim fun _ h => h.ET_eq hw

theorem TwTie.Nlam_iff {Tw : TwForms D} {μ : D.what₂.Tup} (h : TwTie Tw u μ) (hU : UComm (own D u))
    {w : D.what₂.places.Pl} (hw : Formalism.MainNotions.product_first_zeroth_parts.OverT D u w) (x : ((D.fm u).lat 0).V) :
    Tw.e0 u μ x ∈ Nlam (tw Tw u μ) w ↔ x ∈ LT.Nlam D u w :=
  h.elim fun _ h => h.elim fun _ h => h.Nlam_iff hU hw x

theorem TwTie.Nlam_eq_map {Tw : TwForms D} {μ : D.what₂.Tup} (h : TwTie Tw u μ) (hU : UComm (own D u))
    {w : D.what₂.places.Pl} (hw : Formalism.MainNotions.product_first_zeroth_parts.OverT D u w) :
    Nlam (tw Tw u μ) w = (LT.Nlam D u w).map ((Tw.e0 u μ).toLinearMap.restrictScalars (Ow D w)) := by
  ext y
  obtain ⟨x, rfl⟩ := (Tw.e0 u μ).surjective y
  rw [h.Nlam_iff hU hw x]
  constructor
  · exact fun hx => ⟨x, hx, rfl⟩
  · rintro ⟨z, hz, e⟩
    obtain rfl : z = x := (Tw.e0 u μ).injective e
    exact hz

theorem TwTie.sharpBound_twist_iff {Tw : TwForms D} {μ : D.what₂.Tup} (h : TwTie Tw u μ) (hU : UComm (own D u)) :
    Conclusion5Sharp (tw Tw u μ) ↔ TupleChainSharpColumnValuation Tw u μ := by
  refine forall_congr' fun w => ?_
  rw [OverT_tw]
  refine forall_congr' fun hw => forall_congr' fun c => forall_congr' fun n => forall_congr' fun _ => ?_
  rw [h.ET_eq hw]
  refine forall_congr' fun _ => ?_
  constructor
  · intro H x hx
    obtain ⟨y, hy, e⟩ := H (Tw.e0 u μ x) ((h.Nlam_iff hU hw x).mpr hx)
    exact ⟨y, hy, by rw [← Tw.embed_mul_block_embedding]; exact e⟩
  · intro H x' hx
    obtain ⟨x, rfl⟩ := (Tw.e0 u μ).surjective x'
    obtain ⟨y, hy, e⟩ := H x ((h.Nlam_iff hU hw x).mp hx)
    rw [← Tw.embed_mul_block_embedding] at e
    exact ⟨y, hy, e⟩

section Reformulated

variable (D u)

theorem Alcove_own : Alcove (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.Alcove D u := Iff.rfl

theorem levelSetting_chain_iff : HidaSetting (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u := Iff.rfl

theorem upDownIncidence_chain_iff : UpDownIncidenceInverse (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.UpDownIncidenceInverse D u := Iff.rfl

theorem stabilizersTrivial_chain_iff : admS (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.admS D u := Iff.rfl

theorem RoundUp_own : RoundUp (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.RoundUp D u := Iff.rfl

theorem RoundDn_own : RoundDn (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.RoundDn D u := Iff.rfl

theorem TrIso_own : TrIso (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.TrIso D u := Iff.rfl

theorem DiaMul_own : DiaMul (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.DiaMul D u := Iff.rfl

theorem admissibleTorus_chain_iff : admT (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.admT D u := Iff.rfl

theorem firstProperty_chain_iff : Conclusion1 (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.Conclusion1 D u := Iff.rfl

theorem secondProperty_chain_iff : Conclusion2 (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.Conclusion2 D u := Iff.rfl

theorem fourthPropertyExtended_chain_iff : LevelChainUOperatorCommutation (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.LevelChainUOperatorCommutation D u := Iff.rfl

theorem levelChainSharpColumnValuation_ownChain_iff : Conclusion5Sharp (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.Conclusion5Sharp D u := Iff.rfl

theorem sixthProperty_chain_iff : Conclusion6 (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.Conclusion6 D u := Iff.rfl

theorem seventhProperty_chain_iff : division_rows_rational_lattice (own D u) ↔ Formalism.MainNotions.product_first_zeroth_parts.division_rows_rational_lattice D u := Iff.rfl

theorem thirdProperty_chain_iff (C : ℝ) : PointsLemma (own D u) C ↔ Formalism.MainNotions.product_first_zeroth_parts.PointsLemma D u C := Iff.rfl

theorem fourthProperty_chain_iff (C : ℝ) : Conclusion4 (own D u) C ↔ Formalism.MainNotions.product_first_zeroth_parts.Conclusion4 D u C := Iff.rfl

theorem fifthProperty_chain_iff (C : ℝ) : Conclusion5 (own D u) C ↔ Formalism.MainNotions.product_first_zeroth_parts.Conclusion5 D u C := Iff.rfl

theorem weightBudget_chain_iff (L : SizeData₂ D) (C : ℝ) : WeightBudgetBound (own D u) L C ↔ Formalism.MainNotions.product_first_zeroth_parts.WeightBudgetBound D u L C := Iff.rfl

theorem OverT_own (w) : OverT (own D u) w ↔ Formalism.MainNotions.product_first_zeroth_parts.OverT D u w := Iff.rfl

theorem BaseDet_own : BaseDet (own D u) (D.clsLat u) (D.detCls u) ↔ Formalism.MainNotions.product_first_zeroth_parts.admB D u := Iff.rfl

theorem Nlam_own (w) : Nlam (own D u) w = LT.Nlam D u w := rfl

theorem Sram_own (w) : Sram (own D u) w = LT.Sram D u w := rfl

theorem VVT_own (w) : VVT (own D u) w = LT.VVT D u w := rfl

theorem expT_own (w) : expT (own D u) w = LT.expT D u w := rfl

theorem ET_own (w) : ET (own D u) w = EatT D u w := rfl

theorem Wt_own (τ) : Wt (own D u) τ = Wtau D u τ := rfl

theorem Uop_own (i v) : Uop (own D u) i v = LT.Uop D u i v := rfl

theorem Uprod_own (i w) : Uprod (own D u) i w = LT.Uprod D u i w := rfl

theorem Dop_own (i v) : Dop (own D u) i v = Formalism.MainNotions.product_first_zeroth_parts.Dop D u i v := rfl

theorem dia_own (i v a) : dia (own D u) i v a = Formalism.MainNotions.product_first_zeroth_parts.dia D u i v a := rfl

theorem Nm_own (i v) : Nm (own D u) i v = Formalism.MainNotions.product_first_zeroth_parts.Nm D u i v := rfl

theorem trp_own (i v) : trp (own D u) i v = Formalism.MainNotions.product_first_zeroth_parts.trp D u i v := rfl

theorem FFop_own (i v) : FFop (own D u) i v = Formalism.MainNotions.product_first_zeroth_parts.FFop D u i v := rfl

theorem Gs_own (i v) : Gs (own D u) i v = Formalism.MainNotions.product_first_zeroth_parts.Gs D u i v := rfl

theorem GsD_own (i v) : GsD (own D u) i v = Formalism.MainNotions.product_first_zeroth_parts.GsD D u i v := rfl

theorem MramI_own (i) : MramI (own D u) i = Formalism.MainNotions.product_first_zeroth_parts.MramI D u i := rfl

theorem admissibleBasis_chain_iff : admB (own D u) (D.clsLat u) D.muTil (D.detCls u) ↔ Formalism.MainNotions.product_first_zeroth_parts.admB D u :=
  ⟨fun h => h.2.2, fun h => ⟨D.clsLat_lat u, Formalism.MainNotions.GL3Theta.member_chain_has_characters D u, h⟩⟩

end Reformulated

example (w : D.what₂.places.Pl) (h : X.fm.seenP w = false) : ET X w = 0 := by simp [ET, h]

example (w : D.what₂.places.Pl) (h : X.fm.seenP w = false) (i : ℕ) : Uprod X i w = LinearMap.id := by
  simp [Uprod, VVT, h]

example (w : D.what₂.places.Pl) (hw : OverT X w) (e) (eL) :
    ¬ Shared X ⟨X.C, X.A, X.P, { X.fm with seenP := fun w => !X.fm.seenP w }⟩ e eL := by
  rintro ⟨_, _, h⟩
  have := h.seen_eq w hw
  simp at this

end GlobalTheory.LvT
