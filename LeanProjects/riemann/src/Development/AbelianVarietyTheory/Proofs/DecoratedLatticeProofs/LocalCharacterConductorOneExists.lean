import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceCharacterConductorIntegers
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAtTypeAndOrd

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Topology

noncomputable section

namespace GlobalTheory.WeilCondUnif

open GlobalTheory.FinPl GlobalTheory.SplitCharCond

section Local

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem splitPlace_polarisationDatum_inv_integral (p : SplitPt D k) (hU : p.UnitAA) : p.pr (incA D D.host.xi0⁻¹) ∈ 𝒪[k] := by
  obtain ⟨η, hη, h0, h⟩ := exists_idem p
  have hm : (pairA D.host.F 0 η ⊗ₜ[D.host.F] (1 : D.host.E) : AE D) ∈ intAt D (· = p.v) := by
    refine ⟨⟨?_, ?_⟩, AddSubgroup.subset_closure ⟨η, hη, 1, rfl⟩⟩
    · change (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      exact TensorProduct.zero_tmul _ _
    · refine Ideal.mem_iInf.2 fun w => ?_
      change evalV D.host.F w.1 η ⊗ₜ[D.host.F] (1 : D.host.E) = 0
      rw [h0 w.1 w.2, TensorProduct.zero_tmul]
  have := pr_int p (hU.1 _ hm).2.2
  rwa [map_mul, pr_pair_tmul p h, map_one, map_one, mul_one] at this

theorem hasConductor_of_mul {χ ψk : AddChar k Circle} {ξ : k} (hv : valuation k ξ = 1) (he : ∀ x, ψk x = χ (ξ * x))
    (h : HasConductor χ 1) : HasConductor ψk 1 := by
  intro x
  rw [← h x]
  have hξ0 : ξ ≠ 0 := fun h0 => by rw [h0, map_zero] at hv; exact zero_ne_one hv
  constructor
  · intro H y hy
    have := H (ξ⁻¹ * y) (by rw [map_mul, map_inv₀, hv, inv_one, one_mul]; exact hy)
    rwa [he, ← mul_assoc, mul_inv_cancel₀ hξ0, one_mul] at this
  · intro H y hy
    rw [he]
    exact H _ (by rw [map_mul, hv, one_mul]; exact hy)

theorem hasConductor_weil (q : SplitPt D k) (hU : q.UnitAA) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (ψk : AddChar k Circle) (h : (ofSplit q).IsChar ψ ψk) (hx : (ofSplit q).xi ≠ 0) : HasConductor ψk 1 := by
  have h' : ∀ x, (ψk x : ℂ) = psiE ψ (incA D D.host.xi0 * q.sec x) := h
  set ξ : k := q.pr (incA D D.host.xi0) with hξ
  have hξ0 : ξ ≠ 0 := hx
  have hx0 : D.host.xi0 ≠ 0 := fun h0 => hξ0 (by rw [hξ, h0, map_zero, map_zero])
  have hinv : q.pr (incA D D.host.xi0⁻¹) = ξ⁻¹ := map_inv₀ (q.pr.comp (incA D)) D.host.xi0
  have h1 : valuation k ξ ≤ 1 := (Valuation.mem_integer_iff _ _).1 (xi_zero_projection_integral q hU)
  have h2 : valuation k ξ⁻¹ ≤ 1 := by rw [← hinv]; exact (Valuation.mem_integer_iff _ _).1 (splitPlace_polarisationDatum_inv_integral q hU)
  have hv : valuation k ξ = 1 := by
    have hp : valuation k ξ * valuation k ξ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hξ0, map_one]
    refine le_antisymm h1 ?_
    calc (1 : ValueGroupWithZero k) = valuation k ξ * valuation k ξ⁻¹ := hp.symm
      _ ≤ valuation k ξ * 1 := mul_le_mul_right h2 _
      _ = valuation k ξ := mul_one _
  have hχ : q.IsChar ψ (ψk.mulShift ξ⁻¹) := fun a => by
    rw [AddChar.mulShift_apply, h', mul_comm ξ⁻¹ a, ← hinv, sec_mul_pr, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hx0,
      map_one, one_mul]
  refine hasConductor_of_mul hv (fun x => ?_) (hasConductor_one D k q ψ _ hψ hχ hU)
  rw [AddChar.mulShift_apply, ← mul_assoc, inv_mul_cancel₀ hξ0, one_mul]

theorem int_transfer {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : SplitPt D k) (q' : SplitPt D k') (he : q.e = q'.e) (z : AE D) : q.pr z ∈ 𝒪[k] ↔ q'.pr z ∈ 𝒪[k'] := by
  rw [q.int_iff, q'.int_iff, q.sec_pr, q'.sec_pr, he]

theorem dense_transfer {k' : Type} [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : SplitPt D k) (q' : SplitPt D k') (he : q.e = q'.e) (hd : DenseRange (q'.pr.comp (incA D))) :
    DenseRange (q.pr.comp (incA D)) := by
  let f : k' → k := fun y => q.pr (q'.sec y)
  have hf : Continuous f := q.cont_pr.comp q'.cont_sec
  have hs : Function.Surjective f := fun a => ⟨q'.pr (q.sec a), by
    show q.pr (q'.sec (q'.pr (q.sec a))) = a
    rw [q'.sec_pr, ← he, e_mul_sec, q.pr_sec]⟩
  have hc : f ∘ (q'.pr.comp (incA D)) = q.pr.comp (incA D) := funext fun a => by
    show q.pr (q'.sec (q'.pr (incA D a))) = q.pr (incA D a)
    rw [q'.sec_pr, ← he, map_mul, pr_e, one_mul]
  have := hs.denseRange.comp hd hf
  rwa [hc] at this

end Local

section Unif

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {K : Type} [Field K] [NumberField K]

theorem lt_one_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  · rw [← WithZero.exp_log hx] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]; omega

theorem isUnif_of (P : HeightOneSpectrum (𝓞 K)) (ι : K →+* k) (hint : ∀ a, ι a ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt P a)
    (hd : DenseRange ι) (hq : ((Formalism.L2.Col.qOf P : ℕ) : 𝓞 K) ∉ P.asIdeal ^ 2) :
    ∃ ϖ : kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ (ϖ : k) = ι ((Formalism.L2.Col.qOf P : ℕ) : K) := by
  have hvN := GlobalTheory.AtTypeExists.valuation_norm P hq
  set N : K := ((Formalism.L2.Col.qOf P : ℕ) : K) with hN
  have hN0 : N ≠ 0 := fun h0 => WithZero.exp_ne_zero (hvN.symm.trans (by rw [h0, map_zero]))
  have hI : ∀ a, valuation k (ι a) ≤ 1 ↔ P.valuation K a ≤ 1 := fun a => by
    rw [← GlobalTheory.AtTypeExists.intAt_iff, ← hint, Valuation.mem_integer_iff]
  have hvN1 : P.valuation K N ≠ 0 := by rw [hvN]; exact WithZero.exp_ne_zero
  have K1 : ∀ a : K, valuation k (ι a) < 1 → valuation k (ι a) ≤ valuation k (ι N) := by
    intro a ha
    by_cases a0 : a = 0
    · rw [a0, map_zero, map_zero]; exact zero_le'
    have ha0 : valuation k (ι a) ≠ 0 := by
      rw [Ne, Valuation.zero_iff]; exact (map_ne_zero ι).2 a0
    have h1 : ¬ P.valuation K a⁻¹ ≤ 1 := by
      rw [← hI, map_inv₀, map_inv₀]
      intro h
      have := mul_le_mul_right h (valuation k (ι a))
      rw [mul_inv_cancel₀ ha0, mul_one] at this
      exact not_le.2 ha this
    have hPa : P.valuation K a < 1 :=
      lt_of_le_of_ne ((hI a).1 ha.le) (fun h => h1 (by rw [map_inv₀, h, inv_one]))
    have hle := lt_one_le_exp hPa
    have hdiv : P.valuation K (a / N) ≤ 1 := by
      calc P.valuation K (a / N) = P.valuation K a * (P.valuation K N)⁻¹ := by rw [map_div₀, div_eq_mul_inv]
        _ ≤ P.valuation K N * (P.valuation K N)⁻¹ := mul_le_mul_left (hle.trans_eq hvN.symm) _
        _ = 1 := mul_inv_cancel₀ hvN1
    have h2 := (hI _).2 hdiv
    calc valuation k (ι a) = valuation k (ι (a / N)) * valuation k (ι N) := by
          rw [← map_mul, ← map_mul, div_mul_cancel₀ _ hN0]
      _ ≤ 1 * valuation k (ι N) := mul_le_mul_left h2 _
      _ = valuation k (ι N) := one_mul _
  have hexp : WithZero.exp (-1 : ℤ) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num
  have K2 : valuation k (ι N) < 1 := by
    refine lt_of_le_of_ne ((hI N).2 (hvN.trans_le hexp)) fun h => ?_
    have h3 : valuation k (ι N⁻¹) ≤ 1 := by rw [map_inv₀, map_inv₀, h, inv_one]
    rw [hI, map_inv₀, hvN, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h3
    norm_num at h3
  refine ⟨Units.mk0 (ι N) ((map_ne_zero ι).2 hN0), fun x => ⟨fun hx => ?_, fun hx => lt_of_le_of_lt hx K2⟩, rfl⟩
  rw [Units.val_mk0]
  by_cases x0 : x = 0
  · rw [x0, map_zero]; exact zero_le'
  have hx0 : valuation k x ≠ 0 := by rw [Ne, Valuation.zero_iff]; exact x0
  have hs : {y : k | valuation k (y - x) < valuation k x} ∈ 𝓝 x :=
    IsValuativeTopology.mem_nhds_iff'.mpr ⟨Units.mk0 _ hx0, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.1 (hd x) _ hs
  have e : valuation k (ι a) = valuation k x := Valuation.map_eq_of_sub_lt _ hy
  rw [← e] at hx ⊢
  exact K1 a hx

end Unif

theorem cond_unif : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (PP : Pl D.host.E), PP ∈ (pk W).Pg ∨ QAll W PP → ∀ l : LocX a (pk W).βX PP, (∃ ψk : AddChar l.k Circle, (ofSplit l.q).IsChar (pk W).ψ ψk ∧ HasConductor ψk 1) ∧ (∃ ν : Measure l.k, IsUnitVol ν) ∧ (QAll W PP → ∃ ϖ : l.kˣ, GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ ∧ GlobalTheory.SymBridge.IsCompl PP (Formalism.L2.Col.qOf PP) (l.q.pr.comp (incA D)) ϖ) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a PP hPP l
  have hstd : IsStdChar D (pk W).ψ (-1) := W.Q.stdChar
  refine ⟨?_, GlobalTheory.SplitWeil.exists_isUnitVol l.k, fun hQ => ?_⟩
  · obtain ⟨⟨ψk, hψk⟩, -, hxi, -⟩ := GlobalTheory.LocChar.weil_char_split D l.k (ofSplit l.q) (pk W).ψ hstd
    exact ⟨ψk, hψk, hasConductor_weil l.q l.unit _ hstd ψk hψk hxi⟩
  · obtain ⟨t, ht⟩ := hQ
    obtain ⟨⟨p, -, hcard, hp2, -⟩, -⟩ := W.Q.charW.base.lev.Q_pl t PP ht
    have hqp : Formalism.L2.Col.qOf PP = p := by
      rw [← hcard]
      unfold Formalism.L2.Col.qOf
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have hq2 : ((Formalism.L2.Col.qOf PP : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 := by rw [hqp]; exact hp2
    obtain ⟨k', _, _, _, _, q', hqe, -, hint', hd'⟩ := GlobalTheory.LocMod.SplitCompl.exists_place D PP l.q.e l.idem
    have hint : ∀ x, (l.q.pr.comp (incA D)) x ∈ 𝒪[l.k] ↔ Formalism.L2.Col.IntAt PP x := fun x =>
      (int_transfer l.q q' hqe.symm (incA D x)).trans (hint' x)
    have hd := dense_transfer l.q q' hqe.symm hd'
    obtain ⟨ϖ, hu, hϖ⟩ := isUnif_of PP _ hint hd hq2
    exact ⟨ϖ, hu, ⟨hint, hd, rfl, hϖ⟩⟩

end GlobalTheory.WeilCondUnif
