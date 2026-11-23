import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqZeroOfSmulEqZero
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.InjFlat

instance evalLeft_preservesMono (S : Type 1) [Ring S] (c : Scheme.{0}ᵒᵖ) :
    (evaluationLeftAdjoint (ModuleCat.{1} S) c).PreservesMonomorphisms where
  preserves {a b} f _ := by
    have : AB4OfSize.{0} (ModuleCat.{1} S) := AB4OfSize_shrink.{0, 1} _
    rw [NatTrans.mono_iff_mono_app']
    intro t
    have h : ((evaluationLeftAdjoint (ModuleCat.{1} S) c).map f).app t =
        colim.map (Discrete.natTrans (fun _ => f) :
          Discrete.functor (fun _ : c ⟶ t => a) ⟶ Discrete.functor (fun _ : c ⟶ t => b)) := by
      apply Sigma.hom_ext
      intro g
      simp only [evaluationLeftAdjoint_map_app]
      erw [colimit.ι_desc]
      try rfl
    rw [h]
    have : HasExactColimitsOfShape (Discrete (c ⟶ t)) (ModuleCat.{1} S) := inferInstance
    have : PreservesFiniteLimits (colim : (Discrete (c ⟶ t) ⥤ ModuleCat.{1} S) ⥤ _) := inferInstance
    have hm : Mono (Discrete.natTrans (fun _ => f) :
        Discrete.functor (fun _ : c ⟶ t => a) ⟶ Discrete.functor (fun _ : c ⟶ t => b)) :=
      have : ∀ X, Mono ((Discrete.natTrans (fun _ => f) :
          Discrete.functor (fun _ : c ⟶ t => a) ⟶ Discrete.functor (fun _ : c ⟶ t => b)).app X) :=
        fun _ => inferInstanceAs (Mono f)
      NatTrans.mono_of_mono_app _
    exact Functor.map_mono colim _

theorem sec_injective (S : Type) [CommRing S] (M : Shv S) [Injective M] (U : Scheme.{0}) :
    Injective (M.obj.obj (op U)) := by
  have h1 : Injective M.obj :=
    (sheafificationAdjunction Scheme.etaleTopology (ModuleCat.{1} (ULift.{1} S))).map_injective M inferInstance
  exact (evaluationAdjunctionRight (ModuleCat.{1} (ULift.{1} S)) (op U)).map_injective M.obj h1

end GlobalTheory.EtC.InjFlat

namespace GlobalTheory.EtC.InjFlat

theorem zmod_mul_eq_zero (q d e : ℕ) [NeZero q] (hde : d * e = q) (z : ZMod q) (hz : (e : ZMod q) * z = 0) :
    ∃ c : ZMod q, z = c * d := by
  have hq : q ≠ 0 := NeZero.ne q
  have he : e ≠ 0 := by rintro rfl; simp at hde; exact hq hde.symm
  have h1 : q ∣ e * z.val := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_mul, ZMod.natCast_zmod_val, hz]
  have h1' : e * d ∣ e * z.val := by rw [mul_comm e d, hde]; exact h1
  obtain ⟨k, hk⟩ := (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero he)).mp h1'
  refine ⟨k, ?_⟩
  rw [← ZMod.natCast_zmod_val z, hk, Nat.cast_mul, mul_comm]

theorem div_of_injective (q : ℕ) [NeZero q] (N : ModuleCat.{1} (ULift.{1} (ZMod q))) [Injective N] :
    ∀ d e : ℕ, d * e = q → ∀ x : N, d • x = 0 → ∃ y : N, x = e • y := by
  intro d e hde x hx
  let R := ULift.{1} (ZMod q)
  let I : Submodule R R := Submodule.span R {(d : R)}
  have hI : I ≤ LinearMap.ker (LinearMap.lsmul R R (e : R)) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    change (e : R) • (d : R) = 0
    rw [smul_eq_mul, ← Nat.cast_mul, mul_comm, hde]
    ext; simp
  have hJ : I ≤ LinearMap.ker (LinearMap.toSpanSingleton R N x) := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    change (d : R) • x = 0
    rw [Nat.cast_smul_eq_nsmul, hx]
  let i : (R ⧸ I) →ₗ[R] R := I.liftQ _ hI
  let f : (R ⧸ I) →ₗ[R] N := I.liftQ _ hJ
  have hmono : Mono (ModuleCat.ofHom i) := by
    rw [ModuleCat.mono_iff_injective]
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro r hr
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective I r
    rw [LinearMap.mem_ker] at hr
    change (e : R) • r = 0 at hr
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    obtain ⟨c, hc⟩ := zmod_mul_eq_zero q d e hde r.down (by
      have := congrArg ULift.down hr
      rw [smul_eq_mul, ULift.mul_down, ULift.down_natCast] at this
      exact this)
    rw [Submodule.mem_span_singleton]
    refine ⟨ULift.up c, ?_⟩
    apply ULift.down_injective
    rw [hc]
    change (ULift.up c * (d : R)).down = _
    rw [ULift.mul_down, ULift.down_natCast]
  let g := Injective.factorThru (ModuleCat.ofHom f) (ModuleCat.ofHom i)
  have hg := Injective.comp_factorThru (ModuleCat.ofHom f) (ModuleCat.ofHom i)
  refine ⟨g.hom 1, ?_⟩
  have h2 := congrArg (fun φ => φ.hom (Submodule.Quotient.mk (p := I) (1 : R))) hg
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] at h2
  have hi1 : i (Submodule.Quotient.mk 1) = (e : R) := by
    simp only [i]
    erw [Submodule.liftQ_apply]
    simp
  have hf1 : f (Submodule.Quotient.mk 1) = x := by
    simp only [f]
    erw [Submodule.liftQ_apply]
    simp
  rw [hi1, hf1] at h2
  rw [← h2, ← Nat.cast_smul_eq_nsmul R, ← map_smul, smul_eq_mul, mul_one]

theorem flat_of_injective : ∀ (q : ℕ) [NeZero q] (M : Shv (ZMod q)) [Injective M],
    (∀ U : Scheme.{0}, Module.Flat (ULift.{1} (ZMod q)) (Sec M U)) ∧ FlatS M := by
  intro q _ M _
  have hflat : ∀ U : Scheme.{0}, Module.Flat (ULift.{1} (ZMod q)) (Sec M U) := fun U => by
    have := sec_injective (ZMod q) M U
    exact GlobalTheory.ZModFlat.flat_of_divisibility q (Sec M U) (div_of_injective q (M.obj.obj (op U)))
  refine ⟨hflat, M.obj, 𝟙 _, ?_, ?_, fun U _ => hflat U⟩
  · intro U y
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨(M.obj.map g.op).hom y, rfl⟩⟩
  · intro U x hx
    have hx0 : x = 0 := hx
    exact ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => by beta_reduce; rw [hx0, map_zero]⟩

end GlobalTheory.EtC.InjFlat
