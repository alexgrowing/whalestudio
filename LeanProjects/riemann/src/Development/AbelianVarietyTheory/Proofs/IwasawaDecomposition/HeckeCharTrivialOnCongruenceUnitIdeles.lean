import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteChars
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective

noncomputable section

open IsDedekindDomain NumberField Filter Topology

namespace GlobalTheory.LevelChars.LevTriv

open Neutral.B1 Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

open Classical in

theorem prod_localIdele_comp (z : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ)
    (F : Finset (HeightOneSpectrum (𝓞 L))) :
    ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 ∧
    ∀ w, ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L).2 w =
      if w ∈ F then ((z w : (w.adicCompletion L)ˣ) : w.adicCompletion L) else 1 := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨rfl, fun w => by simp; rfl⟩
  | insert a F ha ih =>
    rw [Finset.prod_insert ha, Units.val_mul]
    have e1 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
    have e2 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).2 = x.2 * y.2 := fun _ _ => rfl
    refine ⟨?_, fun w => ?_⟩
    · rw [e1, ih.1, mul_one]; rfl
    · have e : ∀ x y : FiniteAdeleRing (𝓞 L) L, (x * y) w = x w * y w := fun _ _ => rfl
      rw [e2, e, ih.2 w]
      by_cases hw : w = a
      · subst hw
        rw [localIdele_snd_self, if_neg ha, if_pos (Finset.mem_insert_self _ _), mul_one]
      · rw [(localIdele_isSupportedAt L a (z a)).2 w hw, one_mul]
        by_cases hF : w ∈ F
        · rw [if_pos hF, if_pos (Finset.mem_insert_of_mem hF)]
        · rw [if_neg hF, if_neg (fun h => (Finset.mem_insert.1 h).elim hw hF)]

theorem tendsto_prod_localIdele (z : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ) (hz : ∀ v, IsUnitAt v (z v))
    (c : Ideles L) (hc1 : (c : AdeleRing (𝓞 L) L).1 = 1)
    (hc2 : ∀ v, (c : AdeleRing (𝓞 L) L).2 v = ((z v : (v.adicCompletion L)ˣ) : v.adicCompletion L)) :
    Tendsto (fun F : Finset (HeightOneSpectrum (𝓞 L)) => ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L))
      atTop (𝓝 (c : AdeleRing (𝓞 L) L)) := by
  classical
  let A : ∀ w : HeightOneSpectrum (𝓞 L), Set (w.adicCompletion L) := fun w => w.adicCompletionIntegers L
  have hA : ∀ w, ((z w : (w.adicCompletion L)ˣ) : w.adicCompletion L) ∈ A w := fun w => (hz w).le
  let g : Finset (HeightOneSpectrum (𝓞 L)) → ∀ w, A w := fun F w =>
    if w ∈ F then ⟨_, hA w⟩ else ⟨1, one_mem (w.adicCompletionIntegers L)⟩
  let o : ∀ w, A w := fun w => ⟨_, hA w⟩
  have hg : Tendsto g atTop (𝓝 o) := by
    rw [tendsto_pi_nhds]
    intro w
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {w}] with F hF
    have hw : w ∈ F := hF (Finset.mem_singleton_self w)
    simp only [g, o, if_pos hw]
  have h2 := ((RestrictedProduct.isEmbedding_structureMap (A := A) (𝓕 := cofinite)).continuous.tendsto o).comp hg
  have h3 : Tendsto (fun F : Finset (HeightOneSpectrum (𝓞 L)) =>
      ((∏ v ∈ F, localIdele L v (z v) : Ideles L) : AdeleRing (𝓞 L) L).2) atTop (𝓝 (c : AdeleRing (𝓞 L) L).2) := by
    have eo : RestrictedProduct.structureMap _ A cofinite o = (c : AdeleRing (𝓞 L) L).2 := by
      apply Subtype.ext; funext w; exact (hc2 w).symm
    rw [← eo]
    refine Tendsto.congr (fun F => ?_) h2
    apply Subtype.ext; funext w
    show ((g F w : A w) : w.adicCompletion L) = _
    refine Eq.trans ?_ ((prod_localIdele_comp z F).2 w).symm
    by_cases hw : w ∈ F
    · simp only [g, if_pos hw]
    · simp only [g, if_neg hw]
  have h4 := (tendsto_const_nhds (x := (1 : InfiniteAdeleRing L))).prodMk_nhds h3
  have ec : (c : AdeleRing (𝓞 L) L) = ((1 : InfiniteAdeleRing L), (c : AdeleRing (𝓞 L) L).2) := Prod.ext hc1 rfl
  rw [ec]
  refine Tendsto.congr (fun F => ?_) h4
  exact Prod.ext (prod_localIdele_comp z F).1.symm rfl

theorem eq_one_fin (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (ψ : HChar L) (hU : ∀ v, v ∉ S → ψ.UnrAt v)
    (hN : ∀ v ∈ S, ψ.LevelLe v N) (f : Ideles L) (hf1 : (f : AdeleRing (𝓞 L) L).1 = 1)
    (hf : f ∈ GlobalTheory.LevelChars.levSub L S N) : ψ.1 f = 1 := by
  classical
  let u : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ := fun v =>
    ⟨(f : AdeleRing (𝓞 L) L).2 v, ((f⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).2 v,
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) f.mul_inv,
      congrArg (fun y : AdeleRing (𝓞 L) L => y.2 v) f.inv_mul⟩
  have hu : ∀ v, IsUnitAt v (u v) := fun v => (hf v).1
  have hui : ∀ v, IsUnitAt v (u v)⁻¹ := fun v => by
    unfold IsUnitAt
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu v, inv_one]
  have hloc : ∀ v, ψ.1 (localIdele L v (u v)) = 1 := fun v => by
    by_cases hv : v ∈ S
    · exact hN v hv (u v) (hu v) ((hf v).2 hv)
    · exact hU v hv (u v) (hu v)
  let b : Finset (HeightOneSpectrum (𝓞 L)) → Ideles L := fun F => ∏ v ∈ F, localIdele L v (u v)
  have hb1 : ∀ F, ψ.1 (b F) = 1 := fun F => by
    simp only [b, map_prod]
    exact Finset.prod_eq_one fun v _ => hloc v
  have hfi1 : ((f⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := by
    have h := congrArg (fun y : AdeleRing (𝓞 L) L => y.1) f.inv_mul
    have e1 : ∀ x y : AdeleRing (𝓞 L) L, (x * y).1 = x.1 * y.1 := fun _ _ => rfl
    simp only [e1, hf1, mul_one] at h
    exact h
  have t1 := tendsto_prod_localIdele u hu f hf1 fun v => rfl
  have t2 := tendsto_prod_localIdele (fun v => (u v)⁻¹) hui f⁻¹ hfi1 fun v => rfl
  have tb : Tendsto b atTop (𝓝 f) := by
    rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
    refine t1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp (Tendsto.congr (fun F => ?_) t2))
    show ((∏ v ∈ F, localIdele L v (u v)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L) = (((b F)⁻¹ : Ideles L) : AdeleRing (𝓞 L) L)
    congr 1
    simp only [b, map_inv, Finset.prod_inv_distrib]
  have t3 := (ψ.2.1.tendsto f).comp tb
  have t4 : Tendsto (ψ.1 ∘ b) atTop (𝓝 1) := tendsto_const_nhds.congr fun F => (hb1 F).symm
  exact tendsto_nhds_unique t3 t4

theorem infIdele_mem (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) (x : (InfiniteAdeleRing L)ˣ) :
    GlobalTheory.HeckeSplit.infIdele L x ∈ GlobalTheory.LevelChars.levSub L S N := fun v => by
  have e : GlobalTheory.LevelChars.compAt L v (GlobalTheory.HeckeSplit.infIdele L x) = 1 := rfl
  refine ⟨by rw [e, map_one], fun _ => ?_⟩
  rw [e, sub_self, map_zero]
  exact zero_le

theorem infDiag_eq_infIdele (k : Lˣ) :
    infDiag k = GlobalTheory.HeckeSplit.infIdele L (Units.map (algebraMap L (InfiniteAdeleRing L)).toMonoidHom k) := by
  classical
  apply Units.ext
  show ((infDiag k : Ideles L) : AdeleRing (𝓞 L) L) = (algebraMap L (InfiniteAdeleRing L) k, 1)
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, Units.coe_prod]
  let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
    MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
  change ∏ w : InfinitePlace L, ι (Pi.mulSingle w (algebraMap L w.Completion k)) =
    ι (fun w => algebraMap L w.Completion k)
  rw [← map_prod, Finset.univ_prod_mulSingle]

theorem eq_one_inf (ψ : HChar L) (hinf : ∀ k : Lˣ, ψ.inf k = 1) (x : (InfiniteAdeleRing L)ˣ) :
    ψ.1 (GlobalTheory.HeckeSplit.infIdele L x) = 1 := by
  have hc : Continuous (GlobalTheory.HeckeSplit.infIdele L) :=
    Continuous.units_map _ (continuous_id.prodMk continuous_const)
  refine (GlobalTheory.HeckeGal.denseRange_units_inf L).induction_on x
    (isClosed_eq (ψ.2.1.comp hc) continuous_const) fun k => ?_
  rw [← infDiag_eq_infIdele]
  exact hinf k

theorem levSub_triv : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (ψ : Formalism.L2.Host.HChar L), (∀ k : Lˣ, ψ.inf k = 1) → (∀ v, v ∉ S → ψ.UnrAt v) → (∀ v ∈ S, ψ.LevelLe v N) →
    ∀ a ∈ GlobalTheory.LevelChars.levSub L S N, ψ.1 a = 1 := by
  intro L _ _ S N ψ hinf hU hN a ha
  set x := GlobalTheory.HeckeSplit.infPart L a
  have hdec : a = GlobalTheory.HeckeSplit.infIdele L x * ((GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a) := by
    rw [mul_inv_cancel_left]
  have hf1 : (((GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a : Ideles L) : AdeleRing (𝓞 L) L).1 = 1 := by
    rw [← map_inv]
    show ((a⁻¹ : Ideles L) : AdeleRing (𝓞 L) L).1 * (a : AdeleRing (𝓞 L) L).1 = 1
    have h := congrArg (fun y : AdeleRing (𝓞 L) L => y.1) a.inv_mul
    exact h
  have hmem : (GlobalTheory.HeckeSplit.infIdele L x)⁻¹ * a ∈ GlobalTheory.LevelChars.levSub L S N :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ (infIdele_mem S N x)) ha
  rw [hdec, map_mul, eq_one_inf ψ hinf x, eq_one_fin S N ψ hU hN _ hf1 hmem, mul_one]

end GlobalTheory.LevelChars.LevTriv
