import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDoubleCosetOperatorEqInertHeckeOperator
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalMemUnitaryGroupAntidiagonalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalStdLatticeStabilizerMemMaxCompactStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTrivOutsideInertDatumLocalEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertDatumLocalInjectiveOnTrivOutsideStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceIdempotentMulEqSelfOfSupported
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped TensorProduct

namespace GlobalTheory.InertTransport

theorem reps_pull {G H : Type} [Group G] [Group H] (ψ : G →* H) (inj : Function.Injective ψ) (K : Subgroup G) (K' : Set H)
    (hK : ∀ k, k ∈ K ↔ ψ k ∈ K') (hK' : ∀ k ∈ K', ∃ κ, ψ κ = k) (a : G) (R : Finset H)
    (h1 : ∀ γ ∈ R, ∃ k₁ ∈ K', ∃ k₂ ∈ K', γ = k₁ * ψ a * k₂)
    (h2 : ∀ x : H, (∃ k₁ ∈ K', ∃ k₂ ∈ K', x = k₁ * ψ a * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K') :
    ∃ R₀ : Finset G, GlobalTheory.SphLabelOps.Reps K a R₀ ∧
      ∀ (M : Type) [AddCommMonoid M] (F : H → M), ∑ γ ∈ R, F γ = ∑ γ ∈ R₀, F (ψ γ) := by
  have hr : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = ψ (k₁ * a * k₂) := by
    intro γ hγ
    obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := h1 γ hγ
    obtain ⟨κ₁, rfl⟩ := hK' k₁ hk₁
    obtain ⟨κ₂, rfl⟩ := hK' k₂ hk₂
    exact ⟨κ₁, (hK _).2 hk₁, κ₂, (hK _).2 hk₂, by rw [e, map_mul, map_mul]⟩
  refine ⟨R.preimage ψ inj.injOn, ⟨fun γ hγ => ?_, ?_⟩, fun M _ F => ?_⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, e⟩ := hr _ (Finset.mem_preimage.1 hγ)
    exact ⟨k₁, hk₁, k₂, hk₂, inj e⟩
  · rintro _ ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    obtain ⟨γ, ⟨hγ, hx⟩, hu⟩ := h2 (ψ (k₁ * a * k₂)) ⟨_, (hK _).1 hk₁, _, (hK _).1 hk₂, by rw [map_mul, map_mul]⟩
    obtain ⟨l₁, -, l₂, -, rfl⟩ := hr γ hγ
    refine ⟨l₁ * a * l₂, ⟨Finset.mem_preimage.2 hγ, (hK _).2 (by rwa [map_mul, map_inv])⟩, fun δ hδ => inj ?_⟩
    exact hu _ ⟨Finset.mem_preimage.1 hδ.1, by have := (hK _).1 hδ.2; rwa [map_mul, map_inv] at this⟩
  · refine (Finset.sum_preimage ψ R inj.injOn F fun γ hγ hn => ?_).symm
    obtain ⟨k₁, -, k₂, -, e⟩ := hr γ hγ
    exact absurd ⟨_, e.symm⟩ hn

theorem conj_map_eq_one_iff {B C : Type} [CommRing B] [CommRing C] (Ψ : B →+* C) {m k : ℕ}
    (β : Matrix (Fin m) (Fin k) B) (K : Matrix (Fin k) (Fin k) B) (β' : Matrix (Fin k) (Fin m) B)
    (h1 : β * β' = 1) (h2 : β' * β = 1) : (β * K * β').map Ψ = 1 ↔ K.map Ψ = 1 := by
  have e1 : β.map Ψ * β'.map Ψ = 1 := by rw [← Matrix.map_mul, h1]; exact Matrix.map_one _ (map_zero Ψ) (map_one Ψ)
  have e2 : β'.map Ψ * β.map Ψ = 1 := by rw [← Matrix.map_mul, h2]; exact Matrix.map_one _ (map_zero Ψ) (map_one Ψ)
  rw [Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro h
    calc K.map Ψ = (β'.map Ψ * β.map Ψ) * K.map Ψ * (β'.map Ψ * β.map Ψ) := by rw [e2, Matrix.one_mul, Matrix.mul_one]
      _ = β'.map Ψ * (β.map Ψ * K.map Ψ * β'.map Ψ) * β.map Ψ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h, Matrix.mul_one, e2]
  · intro h
    rw [h, Matrix.mul_one, e1]

theorem map_eq_one_iff' {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n : ℕ} (m : Matrix (Fin n) (Fin n) A) :
    m.map φ = 1 ↔ ∀ i j, φ ((m - 1) i j) = 0 := by
  rw [← Matrix.ext_iff]
  refine forall₂_congr fun i j => ?_
  rw [Matrix.sub_apply, map_sub, sub_eq_zero, Matrix.map_apply]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem tensCast_idem {E : Type} [Field E] [NumberField E] {F1 F2 : Subfield E} (h : F1 = F2)
    (w : HeightOneSpectrum (𝓞 E)) (v : HeightOneSpectrum (𝓞 F2))
    (hv : w.asIdeal.comap (algebraMap (𝓞 F2) (𝓞 E)) = v.asIdeal) (α : FiniteAdeleRing (𝓞 F1) F1)
    (h1 : α (w.under (𝓞 F1)) = 1) (h0 : ∀ v', v' ≠ w.under (𝓞 F1) → α v' = 0) :
    ∃ α' : FiniteAdeleRing (𝓞 F2) F2,
      GlobalTheory.NJoin.tensCast h (α ⊗ₜ[F1] (1 : E)) = (1 : E) ⊗ₜ[F2] α' ∧ α' v = 1 ∧ ∀ v', v' ≠ v → α' v' = 0 := by
  subst h
  obtain rfl : w.under (𝓞 F1) = v := HeightOneSpectrum.ext hv
  exact ⟨α, rfl, h1, h0⟩

theorem idem_mul_iff {L : Type} [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L)))
    (α : AFplus L) (h1 : α v = 1) (h0 : ∀ v', v' ≠ v → α v' = 0) (b : AL L) :
    ((1 : L) ⊗ₜ α : AL L) * b = b ↔ ∀ v', v' ≠ v → compAt L v' b = 0 := by
  have c : ∀ u, compAt L u ((1 : L) ⊗ₜ α) = (1 : L) ⊗ₜ (α u) := fun u => rfl
  constructor
  · intro h u hu
    rw [← h, map_mul, c, h0 u hu, TensorProduct.tmul_zero, zero_mul]
  · intro h
    rw [← sub_eq_zero]
    apply GlobalTheory.AL_eq_zero_of_compAt
    intro u
    rw [map_sub, map_mul, c]
    by_cases hu : u = v
    · subst hu
      rw [h1, ← Algebra.TensorProduct.one_def, one_mul, sub_self]
    · rw [h u hu, mul_zero, sub_zero]

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem suppF_iff {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ}
    (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV) {Pp : HeightOneSpectrum (𝓞 D.host.E)}
    {e f : Formalism.L2.Theta.AE D} (hP : Formalism.IndefR.Mult.IsPrimeIdem Pp e f)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hv : NG.OverPl Pp v) (κ : GAf D.host.E n) :
    Formalism.IndefR.Mult.SuppF V f (PV.ψ κ) ↔ TrivOutside {v} κ := by
  obtain ⟨⟨β, β', h1, h2, hm⟩, -⟩ := hV
  have hf := GlobalTheory.AdelicU.Supp.eq_placeIdem_of_isPrimeIdem hP rfl
  obtain ⟨α, hα, hα1, hα0⟩ := GlobalTheory.AdelicU.Supp.isPlaceIdem_placeIdem D (Pp.under (𝓞 D.host.F))
  rw [hα] at hf
  obtain ⟨α', hT, hw1, hw0⟩ := tensCast_idem hF Pp v hv α hα1 hα0
  have hfin : Formalism.L2.Theta.finPart D f = α ⊗ₜ[D.host.F] (1 : D.host.E) := by rw [hf]; rfl
  have hinf : ∀ a b, Formalism.L2.Theta.infPart D ((Formalism.L2.Theta.mt V (PV.ψ κ) - 1) a b) = 0 :=
    (map_eq_one_iff' (Formalism.L2.Theta.infPart D) _).1 (congrArg Units.val (MonoidHom.mem_ker.1 (PV.into κ)))
  have key : ∀ x : Formalism.L2.Theta.AE D, Formalism.L2.Theta.infPart D x = 0 → (f * x = x ↔
      ∀ u, u ≠ v → compAt D.host.E u (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D x)) = 0) := by
    intro x hx
    rw [← idem_mul_iff v α' hw1 hw0, ← hT, ← hfin, ← (GlobalTheory.NJoin.tensCast hF).map_mul, ← (Formalism.L2.Theta.finPart D).map_mul,
      (GlobalTheory.NJoin.tensCast hF).injective.eq_iff]
    refine ⟨fun h => by rw [h], fun h => sub_eq_zero.1 (GlobalTheory.PlaceSupp.AE_eq_zero D _ ?_ ?_)⟩
    · rw [RingHom.map_sub, RingHom.map_mul, hx, mul_zero, sub_zero]
    · rw [RingHom.map_sub, h, sub_self]
  have key2 : ∀ u, (∀ a b, compAt D.host.E u (GlobalTheory.NJoin.tensCast hF (Formalism.L2.Theta.finPart D
      ((Formalism.L2.Theta.mt V (PV.ψ κ) - 1) a b))) = 0) ↔
      (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E u) = 1 := by
    intro u
    let Ψ := (compAt D.host.E u).comp (GlobalTheory.NJoin.tensCast hF).toRingHom
    have e0 := map_eq_one_iff' (Ψ.comp (Formalism.L2.Theta.finPart D)) (Formalism.L2.Theta.mt V (PV.ψ κ))
    have e5 : (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.finPart D) = _ := hm κ
    have e1 : (Formalism.L2.Theta.mt V (PV.ψ κ)).map (Ψ.comp (Formalism.L2.Theta.finPart D)) =
        ((Formalism.L2.Theta.mt V (PV.ψ κ)).map (Formalism.L2.Theta.finPart D)).map Ψ := rfl
    have e2 : ((κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (GlobalTheory.NJoin.tensCast hF).symm).map Ψ =
        (κ.1 : Matrix (Fin n) (Fin n) (AL D.host.E)).map (compAt D.host.E u) :=
      Matrix.ext fun a b => congrArg (compAt D.host.E u) (RingEquiv.apply_symm_apply _ _)
    refine e0.symm.trans ?_
    rw [e1, e5, ← e2]
    exact conj_map_eq_one_iff Ψ β _ β' h1 h2
  constructor
  · intro h u hu
    exact (key2 u).1 fun a b => (key _ (hinf a b)).1 (h a b) u hu
  · intro h a b
    exact (key _ (hinf a b)).2 fun u hu => (key2 u).2 (h u hu) a b

theorem rep_pull {D : D7} (hF : D.host.F = maximalRealSubfield D.host.E) {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ}
    (PV : Formalism.IndefR.principalLevelFrame.RowPsi V n) (hV : GlobalTheory.NJoin.StdFrame hF PV) {Pp : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ}
    (hd : GlobalTheory.Hk3.IsLab V Pp d) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (hv : NG.OverPl Pp v) :
    ∃ (a : GAf D.host.E n) (R₀ : Finset (GAf D.host.E n)), TrivOutside {v} a ∧
      GlobalTheory.SphLabelOps.Reps (GlobalTheory.InertSph.Kv D.host.E n v) a R₀ ∧
      ∀ (M : Type) [AddCommMonoid M] (F : Formalism.L2.Theta.GA D V → M),
        ∑ γ ∈ GlobalTheory.Hk3.rep V Pp d, F γ = ∑ γ ∈ R₀, F (PV.ψ γ) := by
  unfold GlobalTheory.Hk3.rep
  rw [dif_pos hd]
  obtain ⟨e, f, ϖ, α, -, hP, -, -, -, -, -, hα, -, -, hR⟩ := hd.choose_spec
  have hK : ∀ k, k ∈ GlobalTheory.InertSph.Kv D.host.E n v ↔
      PV.ψ k ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} :=
    fun k => and_congr (hV.2 k) (suppF_iff hF PV hV hP hv k).symm
  have h1 : (1 : Formalism.L2.Theta.GA D V) ∈ {k | k ∈ Formalism.L2.Theta.KsphC V ∅ ∧ Formalism.IndefR.Mult.SuppF V f k} := by
    have := (hK 1).1 (one_mem _)
    rwa [map_one] at this
  have hαG : α ∈ Formalism.L2.Theta.GfC V := by
    obtain ⟨γ, ⟨hγ, hx⟩, -⟩ := hR.2 α ⟨1, h1, 1, h1, by rw [one_mul, mul_one]⟩
    have := mul_mem (hR.1 γ hγ).1 hx.1.1
    rwa [mul_inv_cancel_left] at this
  obtain ⟨a, rfl⟩ := PV.onto α hαG
  obtain ⟨R₀, hR₀, hs⟩ := reps_pull PV.ψ PV.inj _ _ hK (fun k hk => PV.onto k hk.1.1) a hd.choose
    (fun γ hγ => (hR.1 γ hγ).2) hR.2
  exact ⟨a, R₀, (suppF_iff hF PV hV hP hv a).1 hα, hR₀, hs⟩

theorem rep_mem {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (Pp : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ)
    {γ : Formalism.L2.Theta.GA D V} (hγ : γ ∈ GlobalTheory.Hk3.rep V Pp d) : γ ∈ Formalism.L2.Theta.GfC V := by
  unfold GlobalTheory.Hk3.rep at hγ
  split_ifs at hγ with hl
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hR⟩ := hl.choose_spec
    exact (hR.1 γ hγ).1
  · simp at hγ

theorem sum_single_one {W : Type*} [AddCommGroup W] [Module ℂ W] (d : List ℤ) (S : List ℤ → W) :
    (Finsupp.single d (1 : ℂ)).sum (fun d z => z • S d) = S d := by
  rw [Finsupp.sum_single_index (h := fun d (z : ℂ) => z • S d) (zero_smul ℂ _), one_smul]

theorem twist_triv {G W : Type*} [Group G] [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W)
    (x : W) (g : G) (h1 : ρ g⁻¹ = 1) : ρ g⁻¹ x = x := by
  rw [h1]; rfl

theorem ext_of_lift {G H W : Type*} [Group G] [Group H] (S : Subgroup G) (r : G →* H) (hs : ∀ u, ∃ g, g ∈ S ∧ r g = u)
    {F F' : H → W} (h : ∀ g ∈ S, F (r g) = F' (r g)) : F = F' := by
  funext u
  obtain ⟨g, hg, rfl⟩ := hs u
  exact h g hg

theorem sum_of_frame {G H W : Type*} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (ψ : G →* H) (S : Subgroup H)
    (onto : ∀ g ∈ S, ∃ x, ψ x = g) (R : Finset H) (R₀ : Finset G) (hs : ∀ F : H → W, ∑ γ ∈ R, F γ = ∑ γ ∈ R₀, F (ψ γ))
    {Φ Φ' : H → W} (e : Φ = Φ') (c : ℂ) (h : ∀ x, ∑ γ ∈ R₀, Φ' (ψ x * ψ γ) = c • Φ' (ψ x)) :
    ∀ g ∈ S, ∑ γ ∈ R, Φ (g * γ) = c • Φ g := by
  intro g hg
  obtain ⟨x, rfl⟩ := onto g hg
  subst e
  exact (hs fun γ => Φ (ψ x * γ)).trans (h x)

theorem sum_fin_abs {G H W : Type*} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] (S : Subgroup G) (r : G →* H)
    (Φ : G → W) (F : H → W) (hext : ∀ g ∈ S, Φ g = F (r g)) (R : Finset G) (hR : ∀ γ ∈ R, γ ∈ S) (c : ℂ) (g : G) (hg : g ∈ S)
    (hc : ∑ γ ∈ R, Φ (g * γ) = c • Φ g) : ∑ γ ∈ R, F (r g * r γ) = c • F (r g) := by
  rw [← hext g hg, ← hc]
  exact Finset.sum_congr rfl fun γ hγ => by rw [hext _ (mul_mem hg (hR γ hγ)), map_mul]

theorem sum_read_abs {G H W W' : Type} [Group G] [Group H] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ψ : G →* H) (eW : W ≃ₗ[ℂ] W') (Φ : H → W) (F : G → W') (b : G) (hreal : ∀ z, F z = eW (Φ (ψ (b⁻¹ * z))))
    {K : Subgroup G} {a : G} {R₀ R₁ : Finset G} (h₀ : GlobalTheory.SphLabelOps.Reps K a R₀) (h₁ : GlobalTheory.SphLabelOps.Reps K a R₁)
    (hfix : ∀ l ∈ K, ∀ z, F (z * l) = F z) (c : ℂ) (hc : ∀ z, ∑ γ ∈ R₁, F (z * γ) = c • F z) (x : G) :
    ∑ γ ∈ R₀, Φ (ψ x * ψ γ) = c • Φ (ψ x) := by
  apply eW.injective
  have hr : ∀ z, eW (Φ (ψ z)) = F (b * z) := fun z => by rw [hreal, inv_mul_cancel_left]
  have e2 := h₀.sum_eq h₁ (one_mem _) (fun γ => F (b * x * γ)) (fun z l hl => by rw [← mul_assoc, hfix l hl])
  rw [map_sum, map_smul, hr, ← hc, ← e2]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← map_mul, hr, one_mul, mul_assoc]

set_option maxHeartbeats 800000 in

theorem eigen_of_fin {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    (j : Fin D.R.m) (t : X.T) (h : DIV.Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (X.R.HV j t).H)
    (hh : GlobalTheory.Hk3.IsOpsV X.R j t h) (Pp : DIV.Pl D.host.E) (hG : GlobalTheory.Hk3.Good X.R t Pp) (d : List ℤ)
    (y : (X.R.HV j t).H) (c : ℂ)
    (hc : ∀ g ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j),
      ∑ γ ∈ GlobalTheory.Hk3.rep (Formalism.IndefR.Links.Vc D j) Pp d, X.R.extV j t y (g * γ) = c • X.R.extV j t y g) :
    h Pp (Finsupp.single d 1) y = c • y := by
  have hcv := (X.given.core.models.cV j).1
  have hext : ∀ g ∈ Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j), X.R.extV j t y g =
      (X.R.HV j t).e y ((Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict g) := fun g hg =>
    twist_triv (X.R.cV j).ρ _ g (hcv g⁻¹ (inv_mem hg))
  have key : (X.R.HV j t).e (h Pp (Finsupp.single d 1) y) = (X.R.HV j t).e (c • y) := by
    refine ext_of_lift (Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j))
      (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict
      (Formalism.IndefR.TopMult.exists_lift (V := Formalism.IndefR.Links.Vc D j)) fun g hg => ?_
    refine (congrFun (hh Pp hG (Finsupp.single d 1) y) _).trans ?_
    refine Eq.trans ?_ (congrFun ((X.R.HV j t).e.map_smul c y) _).symm
    unfold GlobalTheory.Hk3.hkF
    exact (sum_single_one d _).trans (sum_fin_abs (Formalism.L2.Theta.GfC (Formalism.IndefR.Links.Vc D j))
      (Formalism.L2.Theta.finHom (Formalism.IndefR.Links.Vc D j)).rangeRestrict _ _ hext _ (fun γ hγ => rep_mem _ Pp d hγ) c g hg (hc g hg))
  exact X.hinj j t (congrArg (X.R.cV j).ext key)

set_option maxHeartbeats 800000 in

theorem transport_succ {D : D7} {cf : CharFrame D} {nch : NChoice D} {tp : TupTied D cf nch} (X : GlobalTheory.NJoin.RealAt D cf nch tp)
    {M : MtFam D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (A : GlobalTheory.NJoin.Agree X M rep) {μ : D.what₂.Tup}
    (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (k : ℕ) (hk : j.1 + 1 = k) (k1 : 1 ≤ k) (k2 : k ≤ D.R.m)
    (h : DIV.Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (X.R.HV j (X.tupT μ)).H)
    (hh : GlobalTheory.Hk3.IsOpsV X.R j (X.tupT μ) h) (Pp : DIV.Pl D.host.E) (hG : GlobalTheory.Hk3.Good X.R (X.tupT μ) Pp) (d : List ℤ)
    (hd : GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (Dv : InertDatum D.host.E D.R.nV v Pp) (hv : NG.OverPl Pp v) :
    ∃ h0 : Formalism.UG.GU Dv.σw D.R.nV → ℂ, h0 ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw D.R.nV) ∧
      ∀ (f' : D.what₂.Mt μ (j.1 + 1)) (y' : (X.R.HV j (X.tupT μ)).H) (c : ℂ),
        X.R.extV j (X.tupT μ) y' = X.fn hμ j f' →
        (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ →
          NG.rt D.host.E D.R.nV κ ((M μ k k1 k2).real (hk ▸ f')) = (M μ k k1 k2).real (hk ▸ f')) →
        heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((M μ k k1 k2).real (hk ▸ f')) =
          c • (M μ k k1 k2).real (hk ▸ f') →
        h Pp (Finsupp.single d 1) y' = c • y' := by
  subst hk
  have hp := rep_pull A.hF (A.PV j) (A.stdV j) hd hv
  obtain ⟨a, R₀, ha, hR₀, hs⟩ := hp
  have hq := GlobalTheory.InertDCOp.dcOp_eq_heckeFunI D.host.E D.R.nV v Pp Dv
    (GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal _ _ v Pp Dv) (GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact _ _ v Pp Dv) (GlobalTheory.T.exists_trivOutside_inertDatum_local_eq _ _ v Pp Dv) (GlobalTheory.T.inertDatum_local_injective_on_trivOutside _ _ v Pp Dv) a ha
  obtain ⟨R₁, h0, hR₁, hh0, hsum⟩ := hq
  refine ⟨h0, hh0, fun f' y' c hy hfix hc => ?_⟩
  refine eigen_of_fin X j _ h hh Pp hG d y' c fun g hg => ?_
  refine sum_of_frame (A.PV j).ψ _ (A.PV j).onto _ R₀ (hs _) hy c (fun x => ?_) g hg
  exact sum_read_abs (A.PV j).ψ (A.eW μ hμ j) (X.fn hμ j f') ((M μ (j.1 + 1) k1 k2).real f') (A.a j) (A.real μ hμ j f')
    hR₀ hR₁ (fun l hl z => congrFun (hfix l hl.1 hl.2) z) c
    (fun z => (Finset.sum_apply z R₁ fun γ => NG.rt D.host.E D.R.nV γ ((M μ (j.1 + 1) k1 k2).real f')).symm.trans
      (congrFun ((hsum _ _ hfix).trans hc) z)) x

theorem main : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.Conclusion41 D → Formalism.MainNotions.SumRepresentations.adm7 D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv : InertDatum D.host.E D.R.nV v Pp), NG.OverPl Pp v → ∃ h0 : Formalism.UG.GU Dv.σw D.R.nV → ℂ, h0 ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw D.R.nV) ∧ ∀ (f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (y' : (X.R.HV j (X.tupT (D.nd.mu i))).H) (c : ℂ), X.R.extV j (X.tupT (D.nd.mu i)) y' = X.fn hμ j f' → (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ → NG.rt D.host.E D.R.nV κ ((P.M.loc i).real (hj ▸ f')) = (P.M.loc i).real (hj ▸ f')) → heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((P.M.loc i).real (hj ▸ f')) = c • (P.M.loc i).real (hj ▸ f') → h Pp (Finsupp.single d 1) y' = c • y' := by
  intro _ hL D P X A _ _ _ i hμ j hj h hh Pp hG _ d hd v Dv hv
  exact transport_succ X A hμ j (D.nd.j i) hj _ _ h hh Pp hG d hd v Dv hv

end GlobalTheory.InertTransport
