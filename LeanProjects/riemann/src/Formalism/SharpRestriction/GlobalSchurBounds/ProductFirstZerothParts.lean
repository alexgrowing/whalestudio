import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataLatDefs
import Formalism.LocalRingCardinality.DataErr
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant

noncomputable section

namespace Formalism.MainNotions.product_first_zeroth_parts

open Formalism.BasicNotions Classical NumberField

variable (D : D7) (u : D.what₂.Word)

abbrev Fn (i : ℕ) : Type := LT.Fn D u i

abbrev Vl (i : ℕ) : Type := LT.Vl D u i

abbrev Ow (w : D.what₂.places.Pl) : Subring D.what₂.LL := LT.Ow D w

def OverT (w : D.what₂.places.Pl) : Prop := D.what₂.places.resChar w = (D.mem u).A.T

abbrev tops : Finset D.what₂.Tau := topsOf D.host D.eTau

def wsum {n : ℕ} (l : DomWeight n) : ℤ := ∑ i, l.w i

def tpow (n : ℕ) : ℂ := ((D.mem u).A.T : ℂ) ^ n

instance lkModFin (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) : Module.Finite ((D.mem u).A.Fv v) ((D.fm u).lk i v c) :=
  Module.finite_of_finrank_pos (by rw [(D.fm u).lk_rank]; exact D.R.N_pos i)

instance lkDualFintype (i : ℕ) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Fintype (Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) :=
  haveI : Finite (Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)) := Module.finite_of_finite ((D.mem u).A.Fv v)
  Fintype.ofFinite _

abbrev Uop (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i := LT.Uop D u i v

def Dop (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ((D.fm u).te i v c) = 1),
    ((D.fm u).dnT i v c g).toLinearMap ∘ₗ LinearMap.proj ((D.fm u).dn i v c g)

def Eop (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ≠ 0),
    ((D.fm u).dnT i v c g).toLinearMap ∘ₗ LinearMap.proj ((D.fm u).dn i v c g)

def dia (i : ℕ) (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) : Fn D u i →ₗ[ℂ] Fn D u i :=
  LinearMap.pi fun c => ((D.fm u).dilT i v a c).toLinearMap ∘ₗ LinearMap.proj ((D.fm u).dil i v a c)

def Nm (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i := ∑ a : ((D.mem u).A.Fv v)ˣ, dia D u i v a

def trp (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i :=
  (((D.mem u).A.T : ℂ) ^ (D.R.N i - 1))⁻¹ • (Eop D u i v ∘ₗ Uop D u i v)

def FFop (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c) => g ≠ 0),
    ((D.mem u).A.psiT v (g ((D.fm u).te i v c))) • (((D.fm u).dnT i v c g).toLinearMap ∘ₗ LinearMap.proj ((D.fm u).dn i v c g))

def Gs (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i :=
  ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (a : (D.mem u).A.Fv v) • dia D u i v a

def GsD (i : ℕ) (v : (D.mem u).A.vT) : Fn D u i →ₗ[ℂ] Fn D u i :=
  ∑ a : ((D.mem u).A.Fv v)ˣ, (D.mem u).A.psiT v (-(a : (D.mem u).A.Fv v)) • dia D u i v a⁻¹

theorem dia_zero (v : (D.mem u).A.vT) (a : ((D.mem u).A.Fv v)ˣ) : dia D u 0 v a = (D.mem u).A.rhoT v a := by
  apply LinearMap.ext; intro φ; funext c
  rw [(D.fm u).rhoT_dil]; rfl

theorem Nm_zero (v : (D.mem u).A.vT) : Nm D u 0 v = (D.mem u).A.Nm v := by
  simp only [Nm, Formalism.BasicNotions.ColumnsAtT.Nm, dia_zero]

theorem Gs_zero (v : (D.mem u).A.vT) : Gs D u 0 v = (D.mem u).A.gauss v := by
  simp only [Gs, Formalism.BasicNotions.ColumnsAtT.gauss, Formalism.ThetaLiftIndependence.gaussOp, dia_zero]

def MramI (i : ℕ) : Submodule ℂ (Fn D u i) := (D.fm u).Fi i ⊓ ⨅ v, LinearMap.ker (Nm D u i v)

theorem MramI_zero : MramI D u 0 = (D.mem u).A.Mram := by
  simp only [MramI, Formalism.BasicNotions.ColumnsAtT.Mram, Nm_zero, (D.fm u).Fi_zero]

def KT (i : ℕ) : Fn D u i →ₗ[ℂ] Fn D u (i + 1) := (D.mem u).C.Klin i

def colT : Fn D u 0 → Fn D u D.R.m := (D.mem u).C.col

theorem KT_apply (i : ℕ) (φ : Fn D u i) : KT D u i φ = (D.mem u).C.K i φ := rfl

abbrev Wt (τ : D.what₂.Tau) : ℕ := Wtau D u τ

def amax : ℤ := (tops D).fold max 0 (D.fm u).aTop

abbrev VV (w : D.what₂.places.Pl) : Finset (D.mem u).A.vT := LT.VVT D u w

abbrev Uprod (i : ℕ) (w : D.what₂.places.Pl) : Fn D u i →ₗ[ℂ] Fn D u i := LT.Uprod D u i w

def FFall (i : ℕ) : Fn D u i →ₗ[ℂ] Fn D u i :=
  (Finset.univ : Finset (D.mem u).A.vT).toList.foldr (fun v g => (FFop D u i v).comp g) LinearMap.id

def Into {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn D u i → Fn D u j)
    (A : Submodule (Ow D w) (Vl D u i)) (B : Submodule (Ow D w) (Vl D u j)) : Prop :=
  ∀ x ∈ A, ∃ y ∈ B, (D.fm u).emb j y = f ((D.fm u).emb i x)

abbrev imgL {i j : ℕ} (w : D.what₂.places.Pl) (f : Fn D u i →ₗ[ℂ] Fn D u j)
    (A : Submodule (Ow D w) (Vl D u i)) : Submodule (Ow D w) (Vl D u j) := LT.imgL D u w f A

abbrev Sram (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl D u 0) := LT.Sram D u w

def len {i : ℕ} (w : D.what₂.places.Pl) (A B : Submodule (Ow D w) (Vl D u i)) : ℕ∞ :=
  Module.length (Ow D w) (A ⧸ B.comap A.subtype)

def tL {i : ℕ} (w : D.what₂.places.Pl) (n : ℤ) (A : Submodule (Ow D w) (Vl D u i)) :
    Submodule (Ow D w) (Vl D u i) :=
  imgL D u w ((((D.mem u).A.T : ℂ) ^ n) • LinearMap.id) A

abbrev Nlam (w : D.what₂.places.Pl) : Submodule (Ow D w) (Vl D u 0) := LT.Nlam D u w

theorem ram_saturated (x : Vl D u 0) (hx : x ∈ ((D.fm u).lat 0).L) (r : 𝓞 D.what₂.LL) (hr : r ≠ 0)
    (h : r • x ∈ (D.fm u).ramL) : x ∈ (D.fm u).ramL := by
  rw [Formalism.BasicNotions.MemberForms.ramL, Submodule.mem_inf] at h ⊢
  refine ⟨hx, ?_⟩
  have h2 : r • x ∈ (D.fm u).ramSub := h.2
  have hr' : (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r) ≠ 0 := by simpa using hr
  rw [← algebraMap_smul D.what₂.LL r x] at h2
  have h3 := (D.fm u).ramSub.smul_mem (algebraMap (𝓞 D.what₂.LL) D.what₂.LL r)⁻¹ h2
  rw [smul_smul, inv_mul_cancel₀ hr', one_smul] at h3
  exact h3

def Alcove : Prop :=
  ∀ j, j ≤ D.R.m → ∀ τ (a b : Fin (D.R.N j)),
    2 * (((D.fm u).lam j τ).w a - ((D.fm u).lam j τ).w b + (D.R.N j : ℤ)) < ((D.mem u).A.T : ℤ)

def HidaSetting : Prop :=
  2 * D.R.f * D.R.N D.R.m + 1 < (D.mem u).A.T ∧ (4 * amax D u < ((D.mem u).A.T : ℤ) ∧ Alcove D u) ∧
    ∀ τ ∈ tops D, 0 ≤ (D.fm u).bTop τ

def UpDownIncidenceInverse : Prop := (D.fm u).DnUp ∧ (D.fm u).DnFv

def admS : Prop := (D.mem u).C.StabZero

def RoundUp : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v c (x : (D.fm u).lv i v c), (D.fm u).fv i v c x = 1 →
    ∃ e : (D.fm u).lk i v ((D.fm u).up i v c x) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lv i v c,
      e ((D.fm u).te i v ((D.fm u).up i v c x)) = x ∧
      (D.fm u).dn i v ((D.fm u).up i v c x) (((D.fm u).fv i v c).comp e.toLinearMap) = c ∧
      ∀ φ ∈ (D.fm u).Fi i,
        (D.fm u).upT i v c x ((D.fm u).dnT i v ((D.fm u).up i v c x) (((D.fm u).fv i v c).comp e.toLinearMap)
          (φ ((D.fm u).dn i v ((D.fm u).up i v c x) (((D.fm u).fv i v c).comp e.toLinearMap)))) = φ c

def RoundDn : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ((D.fm u).te i v c) = 1 →
    ∃ e : (D.fm u).lv i v ((D.fm u).dn i v c g) ≃ₗ[(D.mem u).A.Fv v] (D.fm u).lk i v c,
      (D.fm u).fv i v ((D.fm u).dn i v c g) = g.comp e.toLinearMap ∧
      (D.fm u).up i v ((D.fm u).dn i v c g) (e.symm ((D.fm u).te i v c)) = c ∧
      ∀ φ ∈ (D.fm u).Fi i,
        (D.fm u).dnT i v c g ((D.fm u).upT i v ((D.fm u).dn i v c g) (e.symm ((D.fm u).te i v c))
          (φ ((D.fm u).up i v ((D.fm u).dn i v c g) (e.symm ((D.fm u).te i v c))))) = φ c

def TrIso : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v c, ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
    (∀ x : (D.fm u).lv i v c, (D.fm u).fv i v c x = 1 →
      (D.fm u).ipV i c ((D.fm u).upT i v c x (φ ((D.fm u).up i v c x))) ((D.fm u).upT i v c x (ψ ((D.fm u).up i v c x))) =
        (D.fm u).ipV i ((D.fm u).up i v c x) (φ ((D.fm u).up i v c x)) (ψ ((D.fm u).up i v c x))) ∧
    (∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c), g ≠ 0 →
      (D.fm u).ipV i c ((D.fm u).dnT i v c g (φ ((D.fm u).dn i v c g))) ((D.fm u).dnT i v c g (ψ ((D.fm u).dn i v c g))) =
        (D.fm u).ipV i ((D.fm u).dn i v c g) (φ ((D.fm u).dn i v c g)) (ψ ((D.fm u).dn i v c g))) ∧
    ∀ a : ((D.mem u).A.Fv v)ˣ,
      (D.fm u).ipV i c ((D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c))) ((D.fm u).dilT i v a c (ψ ((D.fm u).dil i v a c))) =
        (D.fm u).ipV i ((D.fm u).dil i v a c) (φ ((D.fm u).dil i v a c)) (ψ ((D.fm u).dil i v a c))

def DiaMul : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    dia D u i v 1 φ = φ ∧ ∀ a b, dia D u i v (a * b) φ = dia D u i v a (dia D u i v b φ)

def admT : Prop := RoundUp D u ∧ RoundDn D u ∧ TrIso D u ∧ DiaMul D u

def admB : Prop :=
  letI := D.host.cmStar
  ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = ((D.mem u).A.T : D.host.E) ∧
    (∀ w, OverT D u w → ((D.fm u).seenP w = true ↔ 0 < D.what₂.places.val w (D.embE (π : D.host.E)))) ∧
    ∀ i, i ≤ D.R.m →
      ∃ (co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) (L0 : SDLat D.host.E (D.R.N i)),
        (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
        (∀ y, co y ∈ L0.1 ↔ y ∈ (D.sp.X i).L0) ∧
        ∀ c : (D.mem u).C.cls i, ∃ Ln : SDLat D.host.E (D.R.N i),
          (∀ y, co y ∈ Ln.1 ↔ ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
            y = a + D.host.conj (π : D.host.E) • b) ∧
          (QuotientGroup.mk (D.detCls u i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) L0 Ln

def RefAtT : Prop := ∀ w, OverT D u w → D.what₂.muAt w = D.what₂.mu0

def Conclusion1 : Prop :=
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    Uop D u i v φ ∈ (D.fm u).Fi i ∧ Dop D u i v φ ∈ (D.fm u).Fi i ∧ ∀ a, dia D u i v a φ ∈ (D.fm u).Fi i) ∧
  (∀ i, i ≤ D.R.m → ∀ v v', v ≠ v' → ∀ φ ∈ (D.fm u).Fi i,
    Uop D u i v (Uop D u i v' φ) = Uop D u i v' (Uop D u i v φ)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
    (D.fm u).ipC i (Uop D u i v φ) ψ = (D.fm u).ipC i φ (Dop D u i v ψ)) ∧
  (∀ i, i ≤ D.R.m → ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    Into D u w (Uop D u i v) ((D.fm u).Bw i w v) ((D.fm u).S i w) ∧
    Into D u w (Dop D u i v) ((D.fm u).S i w) ((D.fm u).Bw i w v)) ∧
  (∀ i, i ≤ D.R.m → ∀ w, ¬ OverT D u w → ∀ v,
    Into D u w (Uop D u i v) ((D.fm u).S i w) ((D.fm u).S i w) ∧ Into D u w (Dop D u i v) ((D.fm u).S i w) ((D.fm u).S i w)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i, Dop D u i v (Uop D u i v φ) =
    ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ - ((D.mem u).A.T : ℂ) ^ (D.R.N i - 2) • Nm D u i v φ
      + ((D.mem u).A.T : ℂ) ^ (D.R.N i - 2) • trp D u i v φ) ∧
  (∀ v, ∀ x ∈ (D.fm u).ramSub,
    (∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = Uop D u 0 v ((D.fm u).emb 0 x)) ∧
    (∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = Dop D u 0 v ((D.fm u).emb 0 x)) ∧
    ∀ a, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = dia D u 0 v a ((D.fm u).emb 0 x)) ∧
  (∀ w, ¬ OverT D u w → ∀ v,
    Into D u w (Uop D u 0 v) (Sram D u w) (Sram D u w) ∧
    Into D u w (Dop D u 0 v) (Sram D u w) (Sram D u w) ∧
    ∀ a, Into D u w (dia D u 0 v a) (Sram D u w) (Sram D u w)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i,
    Uop D u i v φ ∈ MramI D u i ∧ Dop D u i v φ ∈ MramI D u i ∧
    (∀ a, dia D u i v a φ ∈ MramI D u i) ∧ trp D u i v φ = 0 ∧
    Dop D u i v (Uop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ ∧
    Uop D u i v (Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ)

def Conclusion2 : Prop :=
  ((D.mem u).A.du : ℚ) = (D.duS u : ℚ) * (1 - 1 / (((D.mem u).A.T : ℚ) - 1)) ^ D.R.f ∧
  (D.fm u).ramLat.mu = ((D.fm u).lat 0).mu -
    (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ∧
  (D.fm u).ramLat.muMax ≤ ((D.fm u).lat 0).muMax ∧
  (∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    (0 ≤ ((D.fm u).lam 0 ((D.fm u).tauOf w v)).detShift →
      (D.fm u).S 0 w ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) *
          ((D.duS u : ℚ) * (wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) / (D.R.k : ℚ))) ∧
      len D u w (Sram D u w) (imgL D u w (Uop D u 0 v) (Sram D u w)) ≤
        len D u w ((D.fm u).Bw 0 w v) ((D.fm u).S 0 w) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) +
          len D u w (imgL D u w (Uop D u 0 v) (Sram D u w)) (Sram D u w)) ∧
    (0 ≤ (D.fm u).bTop ((D.fm u).tauOf w v) →
      tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w) ≤ (D.fm u).Bw 0 w v ∧
      (∃ n : ℕ, len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) = n ∧
        (n : ℚ) = (D.what₂.places.ramIdx w : ℚ) * ((D.duS u : ℚ) *
          ((wsum ((D.fm u).lam 0 ((D.fm u).tauOf w v)) : ℚ) + (D.R.k : ℚ) * ((D.fm u).bTop ((D.fm u).tauOf w v) : ℚ)) /
            (D.R.k : ℚ))) ∧
      len D u w (Sram D u w)
          (imgL D u w ((((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • Uop D u 0 v) (Sram D u w)) ≤
        len D u w ((D.fm u).Bw 0 w v) (tL D u w ((D.fm u).bTop ((D.fm u).tauOf w v)) ((D.fm u).S 0 w)) +
          ((D.what₂.places.ramIdx w * ((D.R.k - 1) * D.duS u) : ℕ) : ℕ∞) +
          len D u w (imgL D u w ((((D.mem u).A.T : ℂ) ^ (D.fm u).bTop ((D.fm u).tauOf w v)) • Uop D u 0 v) (Sram D u w))
            (Sram D u w)))

def IsBfam (i : ℕ) (w : D.what₂.places.Pl)
    (BV : Finset (D.mem u).A.vT → Submodule (Ow D w) (Vl D u i)) : Prop :=
  BV ∅ = (D.fm u).S i w ∧ (∀ v, BV {v} = (D.fm u).Bw i w v) ∧
  (∀ V v, v ∈ V → Into D u w (Uop D u i v) (BV V) (BV (V.erase v)) ∧
    Into D u w (Dop D u i v) (BV (V.erase v)) (BV V)) ∧
  (∀ V v, v ∈ V → (D.fm u).tauOf w v ∉ tops D →
    Into D u w (fun φ => tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) • φ) (BV V) (BV (V.erase v)))

def lossK (C : ℝ) : ℕ := ⌊∑ τ, (2 * (Wt D u τ : ℝ) + C * D.R.N D.R.m)⌋₊

def PointsLemma (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    (∀ i, i < D.R.m →
      ((D.fm u).seenP w = false →
        Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) ((D.fm u).S (i + 1) w)) ∧
      ((D.fm u).seenP w = true → ∃ BV, IsBfam D u (i + 1) w BV ∧
        Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) (BV Finset.univ)) ∧
      (∃ e1 : ℕ, (e1 : ℝ) ≤ 4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m ∧
        Into D u w (fun φ => tpow D u e1 • Uprod D u (i + 1) w (KT D u i φ))
          ((D.fm u).S i w) ((D.fm u).S (i + 1) w))) ∧
    (∀ i, i ≤ D.R.m → (D.fm u).seenP w = true → ∀ v, (D.fm u).tauOf w v ∉ tops D →
      Into D u w (fun φ => tpow D u (2 * Wt D u ((D.fm u).tauOf w v) + D.R.t) • φ) ((D.fm u).Bw i w v) ((D.fm u).S i w))

def T4with (bd : D.what₂.places.Pl → (D.mem u).A.vT → ℝ) : Prop :=
  ∀ i, i < D.R.m → ∀ v : (D.mem u).A.vT,
    (∃ c : D.what₂.LL,
      (∀ φ ∈ (D.fm u).Fi i, Uop D u (i + 1) v (KT D u i φ) =
        D.what₂.embLL c • KT D u i (Uop D u i v φ)) ∧
      (∀ σ : D.what₂.LL →+* ℂ, ‖σ c‖ = ((D.mem u).A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2)) ∧
      (∀ w, OverT D u w → ∃ n : ℤ, D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) ∧
        |(n : ℝ)| ≤ (D.what₂.places.ramIdx w : ℝ) * bd w v)) ∧
    (∀ a, ∀ φ ∈ (D.fm u).Fi i, KT D u i (dia D u i v a φ) = dia D u (i + 1) v a (KT D u i φ)) ∧
    ∀ φ ∈ MramI D u i, KT D u i φ ∈ MramI D u (i + 1)

def Conclusion4 (C : ℝ) : Prop :=
  T4with D u (fun w v => (D.R.t : ℝ) + 1 + 2 * Wt D u ((D.fm u).tauOf w v) + C * D.R.N D.R.m)

def LambdaValuationBound (C : ℝ) : Prop := T4with D u (fun _ _ => C * D.R.N D.R.m)

def LevelChainUOperatorCommutation : Prop :=
  ∀ i, i < D.R.m → ∀ v : (D.mem u).A.vT, ∀ φ ∈ (D.fm u).Fi i,
    Uop D u (i + 1) v (KT D u i φ) =
      (((((D.mem u).A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) • KT D u i (Uop D u i v φ)

def Conclusion5 (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    Nlam D u w ≤ Sram D u w ∧
    (∃ e : ℕ, (e : ℝ) ≤ D.R.m * (4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m) +
        ∑ v ∈ VV D u w, ((D.R.t : ℝ) + 1 + 2 * Wt D u ((D.fm u).tauOf w v) + C * D.R.N D.R.m) *
          ((D.R.m : ℝ) * (D.R.m + 1) / 2) ∧
      Into D u w (fun φ => tpow D u e • colT D u φ) (Nlam D u w) ((D.fm u).S D.R.m w)) ∧
    (∃ n : ℕ, len D u w (Sram D u w) (Nlam D u w) = n ∧
      (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * ∑ v ∈ VV D u w,
        ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v) + D.R.k + (D.fm u).bTop ((D.fm u).tauOf w v))))

def ETpi : ℝ :=
  2 * ∑ τ, (Wt D u τ : ℝ) + (D.R.f : ℝ) * D.R.N D.R.m +
    ((tops D).card : ℝ) * ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) / 4

abbrev ET (w : D.what₂.places.Pl) : ℝ := EatT D u w

theorem ET_eq (w : D.what₂.places.Pl) : ET D u w = if (D.fm u).seenP w then ETpi D u else 0 := rfl

def Conclusion5Sharp : Prop :=
  ∀ w, OverT D u w → ∀ (c : D.what₂.LL) (n : ℤ), D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) →
    (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * ET D u w) ≤ (n : ℝ) →
    Into D u w (fun φ => D.what₂.embLL c • colT D u φ) (Nlam D u w) ((D.fm u).S D.R.m w)

def ETDef (L : SizeData₂ D) : Prop :=
  ∀ w, OverT D u w → L.tau w = 0 ∧
    ∀ j ∈ SizeData₂.lifts D, L.gain j w = 0 ∧ L.F j w = 0 ∧ L.E u j w = ET D u w

def WeightBudgetBound (L : SizeData₂ D) (C : ℝ) : Prop :=
  (∀ S : Finset D.what₂.places.Pl, (∀ w ∈ S, OverT D u w) →
    0 ≤ ∑ w ∈ S, SizeData₂.sz w (ET D u w) ∧
    ∑ w ∈ S, SizeData₂.sz w (ET D u w) ≤ ETpi D u * Real.log ((D.mem u).A.T : ℝ)) ∧
  ETpi D u * Real.log ((D.mem u).A.T : ℝ) ≤ C * L.B0

def Pt : Fn D u D.R.m →ₗ[ℂ] (D.mem u).P.Wrow := (D.mem u).P.lowerMap ∘ₗ (D.mem u).P.evz

def ptB : ℝ := ∏ τ, ((D.mem u).A.T : ℝ) ^ (-((D.fm u).deg τ)) * (D.fm u).beOn τ ^ 2

def Conclusion6 : Prop :=
  Function.Injective (D.fm u).til ∧
  (∀ c, Function.Bijective ((D.fm u).stabMap c)) ∧
  (∀ φ ∈ (D.fm u).Fi D.R.m, Pt D u φ ∈ (D.fm u).ptC) ∧
  (∃ h : (D.fm u).PRat, (D.fm u).PtilIntegral h ∧
    ∀ (v : InfinitePlace D.what₂.LL) (x : Vl D u D.R.m),
      (Formalism.HermitianLatticesTheory.majAt (D.fm u).ptLat.b (D.fm u).ptLat.X v ((D.fm u).PtL h x) ((D.fm u).PtL h x)).re ≤
        ptB D u * (Formalism.HermitianLatticesTheory.majAt ((D.fm u).lat D.R.m).b ((D.fm u).lat D.R.m).X v x x).re) ∧
  ∀ φ ∈ (D.fm u).Fi D.R.m, ((D.fm u).ipP (Pt D u φ) (Pt D u φ)).re ≤ ptB D u * ((D.fm u).ipC D.R.m φ φ).re

def division_rows_rational_lattice : Prop :=
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i, FFop D u i v φ = Dop D u i v (Gs D u i v φ)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    Gs D u i v (GsD D u i v φ) = ((D.mem u).A.T : ℂ) • φ - Nm D u i v φ) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i, FFop D u i v φ ∈ MramI D u i) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i, ∀ ψ ∈ MramI D u i,
    (D.fm u).ipC i (FFop D u i v φ) (FFop D u i v ψ) = ((D.mem u).A.T : ℂ) ^ D.R.N i * (D.fm u).ipC i φ ψ) ∧
  (∀ i, i ≤ D.R.m → ∀ φ ∈ MramI D u i, ∀ ψ ∈ MramI D u i,
    (D.fm u).ipC i (FFall D u i φ) (FFall D u i ψ) = ((D.mem u).A.T : ℂ) ^ (D.R.f * D.R.N i) * (D.fm u).ipC i φ ψ) ∧
  (∀ i, i < D.R.m → ∀ v, ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ MramI D u i,
    FFop D u (i + 1) v (KT D u i φ) = c • KT D u i (FFop D u i v φ))

section Tensor

variable {ι : Type} [Fintype ι]

def ten {R : Type} [CommRing R] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) R) :
    MvPolynomial (ι × Fin n × Fin n) R :=
  ∏ τ, MvPolynomial.rename (Prod.mk τ) (f τ)

def blk {n n' : ℕ} (F : ι → MvPolynomial (Fin n × Fin n) ℂ → MvPolynomial (Fin n' × Fin n') ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (ι × Fin n' × Fin n') ℂ :=
  (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).constr ℂ fun mon =>
    ten fun τ => F τ (MvPolynomial.monomial
      (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1)

def nfAll {n : ℕ} (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) : ℂ :=
  Formalism.REAL.fockF p q / ∏ τ, Formalism.REAL.fockF (extremal ℂ n (lam τ)) (extremal ℂ n (lam τ))

def CSpan {n : ℕ} (lam : ι → DomWeight n) : Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  Submodule.span ℂ {p | ∃ f : ι → MvPolynomial (Fin n × Fin n) ℂ,
    (∀ τ, f τ ∈ delSq ℂ n (lam τ)) ∧ p = ten f}

lemma comap_sum {α : Type} (v : ι → (α →₀ ℕ)) (τ : ι) :
    (∑ σ, (v σ).mapDomain (Prod.mk σ)).comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn = v τ := by
  ext a
  rw [Finsupp.comapDomain_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single τ]
  · exact Finsupp.mapDomain_apply (Prod.mk_right_injective τ) _ a
  · intro b _ hb
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact hb (congrArg Prod.fst hy)
  · intro h; exact absurd (Finset.mem_univ τ) h

lemma ten_monomial {n : ℕ} (v : ι → ((Fin n × Fin n) →₀ ℕ)) :
    ten (fun τ => MvPolynomial.monomial (v τ) (1 : ℂ)) =
      MvPolynomial.monomial (∑ σ, (v σ).mapDomain (Prod.mk σ)) 1 := by
  unfold ten
  simp only [MvPolynomial.rename_monomial]
  rw [MvPolynomial.monomial_sum_one]

def tenM (n : ℕ) : MultilinearMap ℂ (fun _ : ι => MvPolynomial (Fin n × Fin n) ℂ)
    (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  (MultilinearMap.mkPiAlgebra ℂ ι (MvPolynomial (ι × Fin n × Fin n) ℂ)).compLinearMap
    (fun τ => (MvPolynomial.rename (Prod.mk τ) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] _).toLinearMap)

lemma tenM_apply (n : ℕ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) : tenM n f = ten f := by
  simp [tenM, ten]

theorem blk_ten {n n' : ℕ}
    (F : ι → MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n' × Fin n') ℂ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    blk (fun τ => F τ) (ten f) = ten (fun τ => F τ (f τ)) := by
  have key : (blk (n := n) (n' := n') (fun τ => F τ)).compMultilinearMap (tenM (ι := ι) n) =
      (tenM (ι := ι) n').compLinearMap F := by
    apply Module.Basis.ext_multilinear (fun _ => MvPolynomial.basisMonomials (Fin n × Fin n) ℂ)
    intro v
    simp only [LinearMap.compMultilinearMap_apply, MultilinearMap.compLinearMap_apply, tenM_apply,
      MvPolynomial.coe_basisMonomials]
    rw [ten_monomial]
    have hc := (MvPolynomial.basisMonomials (ι × Fin n × Fin n) ℂ).constr_basis ℂ
      (fun mon => ten fun τ => F τ (MvPolynomial.monomial
        (mon.comapDomain (Prod.mk τ) (Prod.mk_right_injective τ).injOn) 1))
      (∑ σ, (v σ).mapDomain (Prod.mk σ))
    simp only [MvPolynomial.coe_basisMonomials] at hc
    unfold blk
    rw [hc]
    simp only [comap_sum]
  have h1 := congrArg (fun g => g f) key
  simpa [tenM_apply] using h1

end Tensor

def IntSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ Ow D w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = D.what₂.embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

lemma Nm_succ (R : Ranks) : R.N R.m - 1 + 1 = R.N R.m := Nat.sub_add_cancel (Ranks.N_pos R R.m)

def wSh {n : ℕ} (l : DomWeight n) (c : ℤ) : DomWeight n where
  w := fun i => l.w i - c
  anti := fun _ _ h => sub_le_sub_right (l.anti h) c

def cTw (R : Ranks) : ℤ := ((R.m * (R.t + 1) / 2 : ℕ) : ℤ)

def lamTr (τ : D.what₂.Tau) : DomWeight (D.R.N D.R.m) := wSh ((D.fm u).lam D.R.m τ) (cTw D.R)

def sgTr (τ : D.what₂.Tau) : DomWeight (D.R.N D.R.m - 1) := wSh ((D.fm u).sg τ) (cTw D.R)

theorem detShift_wSh {n : ℕ} (l : DomWeight n) (c : ℤ) (hn : 0 < n) : (wSh l c).detShift = l.detShift - c := by
  simp [DomWeight.detShift, hn, wSh]

theorem natW_wSh {n : ℕ} (l : DomWeight n) (c : ℤ) : (wSh l c).natW = l.natW := by
  funext i
  have hn : 0 < n := Fin.pos i
  unfold DomWeight.natW
  rw [detShift_wSh l c hn]
  congr 1
  show l.w i - c - (l.detShift - c) = l.w i - l.detShift
  ring

theorem delSq_wSh (R : Type) [CommRing R] {n : ℕ} (l : DomWeight n) (c : ℤ) : delSq R n (wSh l c) = delSq R n l := by
  unfold delSq; rw [natW_wSh]

theorem extremal_wSh (R : Type) [CommRing R] {n : ℕ} (l : DomWeight n) (c : ℤ) :
    extremal R n (wSh l c) = extremal R n l := by
  unfold extremal; rw [natW_wSh]

theorem interlaceTr (h : (D.fm u).SgInterlace) (τ : D.what₂.Tau) :
    Formalism.MainNotions.PrimeDegreeVariant.Interlace (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) :=
  fun i => ⟨sub_le_sub_right (h τ i).1 _, sub_le_sub_right (h τ i).2 _⟩

def sqrtT : ℂˣ := Units.mk0 ((Real.sqrt ((D.mem u).A.T : ℝ) : ℝ) : ℂ) (by
  have h : 0 < ((D.mem u).A.T : ℝ) := by exact_mod_cast (D.mem u).A.T_prime.pos
  exact_mod_cast (Real.sqrt_pos.mpr h).ne')

def gFull (g : GL (Fin (D.R.N D.R.m - 1)) ℂ) : GL (Fin (D.R.N D.R.m)) ℂ :=
  Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ _ _ (Nm_succ D.R) g * Formalism.MainNotions.PrimeDegreeVariant.lastGL ℂ _ (sqrtT D u)

def opNorm (τ : D.what₂.Tau) (b : MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ) : ℝ :=
  sSup ((fun f => Real.sqrt ((normFock ((D.fm u).sg τ) (b f) (b f)).re /
      (normFock ((D.fm u).lam D.R.m τ) f f).re)) '' {f | f ∈ delSq ℂ _ ((D.fm u).lam D.R.m τ) ∧ f ≠ 0})

structure Pend where

  br : D.what₂.Tau → (MvPolynomial (Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ →ₗ[ℂ]
    MvPolynomial (Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ)

  coM : D.what₂.places.Pl → (D.fm u).clsP → (((D.mem u).C.Y D.R.m → ℂ) →ₗ[ℂ]
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m) × Fin (D.R.N D.R.m)) ℂ)

  coP : D.what₂.places.Pl → ((D.mem u).P.Wrow →ₗ[ℂ] ((D.fm u).clsP →
    MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ))
  coM_mem : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coM w c (φ ((D.fm u).til c)) ∈ CSpan ((D.fm u).lam D.R.m)
  coM_inj : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, coM w c (φ ((D.fm u).til c)) = 0 → φ ((D.fm u).til c) = 0
  coP_mem : ∀ w, ∀ z ∈ (D.fm u).ptC, ∀ c, coP w z c ∈ CSpan (D.fm u).sg
  coP_inj : ∀ w, ∀ z ∈ (D.fm u).ptC, coP w z = 0 → z = 0

  Pt_eq : ∀ w, ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ c,
    coP w (Pt D u φ) c = blk (fun τ => br τ) (coM w c (φ ((D.fm u).til c)))

  lat_co : ∀ w, ∀ x ∈ (D.fm u).S D.R.m w, ∀ c,
    coM w c ((D.fm u).emb D.R.m x ((D.fm u).til c)) ∈ IntSpan D w ((D.fm u).lam D.R.m)

  pt_co : ∀ w, ∀ z ∈ (D.fm u).ptC, (∃ y ∈ (D.fm u).SP w, (D.fm u).ptEmb y = z) ↔ ∀ c, coP w z c ∈ IntSpan D w (D.fm u).sg

  gP : D.what₂.places.Pl → (D.fm u).clsP → D.what₂.Tau → GL (Fin (D.R.N D.R.m - 1)) ℂ

  ipV_co : ∀ w c, ∀ φ ∈ (D.fm u).Fi D.R.m, ((D.fm u).ipV D.R.m ((D.fm u).til c) (φ ((D.fm u).til c)) (φ ((D.fm u).til c))).re =
    (nfAll ((D.fm u).lam D.R.m)
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coM w c (φ ((D.fm u).til c))))
      (blk (fun τ => sqAct ℂ _ (lamTr D u τ) (gFull D u (gP w c τ))) (coM w c (φ ((D.fm u).til c))))).re

  re_petersson_self_eq_sum_coord : ∀ w, ∀ z ∈ (D.fm u).ptC, ((D.fm u).ipP z z).re = ∑ c, ((Nat.card ((D.fm u).stabilizer₂ c) : ℝ))⁻¹ *
    (nfAll (D.fm u).sg (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP w z c))
      (blk (fun τ => sqAct ℂ _ (sgTr D u τ) (gP w c τ)) (coP w z c))).re

  beOn_eq : ∀ τ, (D.fm u).beOn τ = opNorm D u τ (br τ)

  interlace : (D.fm u).SgInterlace

variable {D u}

def ArchimedeanSignatureMatching (P : Pend D u) : Prop :=
  ∀ τ, Formalism.MainNotions.PrimeDegreeVariant.IsBr (Nm_succ D.R) (lamTr D u τ) (sgTr D u τ) (P.br τ)

structure Th22 (D : D7) where
  cc : Ideal (𝓞 D.host.K)
  δ : ℂ
  χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ
  e : Formalism.MainNotions.TaylorLogMetric.FamE D
  cc_curve : Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc
  δ_delta : Formalism.MainNotions.TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ
  χ_chi : Formalism.MainNotions.TaylorLogMetric.IsChi D χ

def Th22.Tr (G : Th22 D) : Formalism.MainNotions.TaylorLogMetric.Tor D := Formalism.MainNotions.TaylorLogMetric.tor0 D G.cc G.δ

def adm1 (G : Th22 D) : Prop := Formalism.MainNotions.TaylorLogMetric.vec22 D G.Tr G.e ∧ Formalism.MainNotions.TaylorLogMetric.eq22 D G.Tr G.χ G.e

def adm2 (G : Th22 D) : Prop := Formalism.MainNotions.TaylorLogMetric.int22 D G.Tr G.e

def adm3 (G : Th22 D) : Prop := Formalism.MainNotions.TaylorLogMetric.mom22 D G.cc G.δ G.e

def ChiTie (G : Th22 D) : Prop :=
  ∃ idl : D.Dt ⧸ D.UO → Formalism.MainNotions.TaylorLogMetric.IdE D, Formalism.MainNotions.TaylorLogMetric.RelDetPinned D idl ∧ G.χ = Formalism.MainNotions.TaylorLogMetric.chiRec D idl

theorem relative_determinant_equation_of_admissible (G : Th22 D) (h : adm1 G) (t : ChiTie G) : Formalism.MainNotions.TaylorLogMetric.RelativeDeterminantEquation D G.Tr G.e := by
  obtain ⟨idl, hpin, hχ⟩ := t
  unfold adm1 Formalism.MainNotions.TaylorLogMetric.eq22 at h
  obtain ⟨-, h1, h2, h3⟩ := h
  letI := D.host.cmStar
  have key : ∀ N (L L' : SDLat D.host.E N),
      G.χ (Formalism.MainNotions.TaylorLogMetric.detId D L.1 L'.1) = ((Formalism.MainNotions.TaylorLogMetric.chiQ D (D.relDet N L L') : ℂˣ) : ℂ) := by
    intro N L L'
    rw [hχ, ← hpin.2.2.2.2 N L L']
    unfold Formalism.MainNotions.TaylorLogMetric.chiRec
    have hex : ∃ x, idl x = idl (D.relDet N L L') := ⟨_, rfl⟩
    rw [dif_pos hex]
    exact congrArg (fun x => ((Formalism.MainNotions.TaylorLogMetric.chiQ D x : ℂˣ) : ℂ)) (hpin.1 hex.choose_spec)
  unfold Formalism.MainNotions.TaylorLogMetric.RelativeDeterminantEquation
  refine ⟨h1, fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · rw [h2 N N' L L' L'' hN hN']
    simp only [key, Units.val_zpow_eq_zpow_val]
  · rw [h3 N N' L L₁ L' hN hN']
    simp only [key, Units.val_zpow_eq_zpow_val]

def admitted (P : Pend D u) (G : Th22 D) : Prop :=
  UpDownIncidenceInverse D u ∧ admS D u ∧ adm1 G ∧ adm2 G ∧ adm3 G ∧ ArchimedeanSignatureMatching P ∧ admT D u ∧ admB D u

def AdmE (D : D7) (u : D.what₂.Word) : Prop := ∃ (P : Pend D u) (G : Th22 D), admitted P G

def Conclusion₂ (D : D7) (u : D.what₂.Word) (C : ℝ) : Prop :=
  Conclusion1 D u ∧ Conclusion2 D u ∧ PointsLemma D u C ∧ Conclusion4 D u C ∧ Conclusion5 D u C ∧ Conclusion6 D u ∧ division_rows_rational_lattice D u ∧ LevelChainUOperatorCommutation D u ∧ Conclusion5Sharp D u

def Stmt (D : D7) (u : D.what₂.Word) (C : ℝ) : Prop := HidaSetting D u → AdmE D u → Conclusion₂ D u C

def ConclusionOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    HidaSetting (Fm.D x i) u → Conclusion₂ (Fm.D x i) u C

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), AdmE (Fm.D x i) u

def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop := AdmF Fm → ConclusionOnFamily Fm C

def ExistsConstFamilyConclusionsOfHypotheses {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → ∃ C : ℝ, ConclusionOnFamily Fm C

def FamilyEventuallyPointwiseAtConst {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word), Stmt (Fm.D x i) u C

def ShareFamilyAtConstant {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∃ C : ℝ, FamilyEventuallyPointwiseAtConst Fm C

theorem family_statement_of_pointwise_const {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) (h : FamilyEventuallyPointwiseAtConst Fm C) : KudlaFamilyStatement Fm C := by
  rintro ⟨x1, hA⟩
  obtain ⟨x0, hS⟩ := h
  exact ⟨max x0 x1, fun x hx i u hs =>
    hS x (le_trans (le_max_left _ _) hx) i u hs (hA x (le_trans (le_max_right _ _) hx) i u)⟩

theorem family_statement_exists_of_pointwise {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (h : ShareFamilyAtConstant Fm) : ExistsConstFamilyConclusionsOfHypotheses Fm := by
  obtain ⟨C, hC⟩ := h
  intro hA
  exact ⟨C, family_statement_of_pointwise_const Fm C hC hA⟩

def BudF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x, x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    HidaSetting (Fm.D x i) u → WeightBudgetBound (Fm.D x i) u (Fm.L x i) C

def ShareAbsoluteConstant (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ C : ℝ, ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), 𝒞 Fm → FamilyEventuallyPointwiseAtConst Fm C

end Formalism.MainNotions.product_first_zeroth_parts
