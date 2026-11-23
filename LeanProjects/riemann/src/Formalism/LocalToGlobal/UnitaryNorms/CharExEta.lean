import Formalism.LocalToGlobal.UnitaryNorms.CharExHost

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

section Gen

variable (L : Type) [Field L] [NumberField L]

theorem mulSupport_ord_finite (c : HeightOneSpectrum (𝓞 L) → ℂˣ) (x : Ideles L) :
    (Function.mulSupport fun v => c v ^ ordAt L v x).Finite := by
  refine (Filter.eventually_cofinite.mp (ordAt_eventually L x)).subset fun v hv h0 => hv ?_
  show c v ^ ordAt L v x = 1
  rw [h0, zpow_zero]

def unrQ (c : HeightOneSpectrum (𝓞 L) → ℂˣ) : Ideles L →* ℂˣ where
  toFun x := ∏ᶠ v, c v ^ ordAt L v x
  map_one' := by simp only [ordAt_one, zpow_zero, finprod_one]
  map_mul' x y := by
    simp only [ordAt_mul, zpow_add]
    exact finprod_mul_distrib (mulSupport_ord_finite L c x) (mulSupport_ord_finite L c y)

variable {L}

theorem unrQ_unit (c : HeightOneSpectrum (𝓞 L) → ℂˣ) {u : Ideles L} (hu : u ∈ unitIdeles L) : unrQ L c u = 1 := by
  show ∏ᶠ v, c v ^ ordAt L v u = 1
  have h : ∀ v, c v ^ ordAt L v u = 1 := fun v => by rw [(ordAt_eq_zero_iff L v u).mpr (hu v), zpow_zero]
  simp only [h, finprod_one]

theorem continuous_of_unit (hO : OpenUnits L) (Φ : Ideles L →* ℂˣ) (h : ∀ u ∈ unitIdeles L, Φ u = 1) : Continuous Φ := by
  refine continuous_of_continuousAt_one Φ ?_
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  exact Filter.mem_of_superset (hO.mem_nhds (one_mem _)) fun u hu => (h u hu).symm

open Classical in

def InfChar {I : Type} [Fintype I] (φ : I → L →+* ℂ) (n : I → ℤ) : Prop :=
  ∃ Φ : Ideles L →* ℂˣ, Continuous Φ ∧ (∀ x, ‖((Φ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ v x, Φ (localIdele L v x) = 1) ∧
    (∀ k : Lˣ, ((Φ (diagUnits L k) : ℂˣ) : ℂ) = ∏ i, (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ∧
    ∀ (S : Finset (InfinitePlace L)) (k : Lˣ), ((Φ (∏ w ∈ S, infIdele L w (atInf w k)) : ℂˣ) : ℂ) =
      ∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (φ i) ∈ S), (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i

end Gen

variable {R : Formalism.BasicNotions.Ranks} (H : Formalism.BasicNotions.Host R)

def cEta (P : HeightOneSpectrum (𝓞 H.E)) : ℂˣ :=
  if (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1 then -1 else 1

def etaVal (k : H.Eˣ) : ℂ :=
  ((unrQ H.E (cEta H) (diagUnits H.E k) : ℂˣ) : ℂ) *
    ∏ τ, (embPsi H τ (k : H.E) / ((‖embPsi H τ (k : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)

def EtaFinCheck : Prop := ∀ v k, unrQ H.E (cEta H) (aF H.F v k) = etaFin (L := H.E) H.F v k

open Classical in

def EtaInfCheck : Prop := ∀ (w : InfinitePlace H.F) (k : H.Fˣ),
  (∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (embPsi H i) ∈ aboveInf (L := H.E) H.F w),
    (embPsi H i ((upF H.F k : H.Eˣ) : H.E) / ((‖embPsi H i ((upF H.F k : H.Eˣ) : H.E)‖ : ℝ) : ℂ)) ^ (1 : ℤ)) =
    ((etaInf H.F w k : ℂˣ) : ℂ)

def EtaGlob : Prop := ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F → etaVal H k = 1

def GlobForm : Prop := ∀ k : H.Eˣ, diagUnits H.E k ∈ unitF (L := H.E) H.F →
  ∃ a : H.Fˣ, k = upF H.F a ∨ ∃ s : H.Eˣ, (s : H.E) = H.sqrtMinusD ∧ k = s * upF H.F a

def EtaRecF : Prop := ∀ a : H.Fˣ, etaVal H (upF H.F a) = 1

def EtaSqrtD : Prop := ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD → etaVal H s = 1

end CharEx

end Formalism.L2.Host
