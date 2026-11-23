import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumHeckeEigenvalueGeneratingSeriesGL

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem unramB_tprod_ne_zero {ι : Type} [Fintype ι] {X : ι → Type} [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (v : ∀ i, X i) (hv : ∀ i, v i ≠ 0) : PiTensorProduct.tprod ℂ v ≠ 0 := by
  classical
  choose l hl using fun i => Module.Projective.exists_dual_eq_one ℂ (hv i)
  intro h0
  have := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap l)) h0
  simp [hl] at this

theorem unramB_irr_quot (w : HeightOneSpectrum (𝓞 E)) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) (hρs : IsSmooth ρ) {f0 : V} (hf0ne : f0 ≠ 0)
    (hf0K : f0 ∈ fixed ρ (GlobalTheory.LFun.KGL w n)) (B : Multiset ℂˣ)
    (hsat : ∀ f ∈ fixed ρ (GlobalTheory.LFun.KGL w n), f ≠ 0 → GlobalTheory.LFun.IsSatVecGL w ρ f B) :
    ∃ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ ρ ∧
      GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w n) ∧ GlobalTheory.LFun.HasSatGL w P.ρ B := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n

  obtain ⟨W, _, _, π, q, hπ, hq, hq0⟩ :=
    GlobalTheory.FinZeta.GLSeries.exists_irrSmooth_quot (ρ) hKo hf0ne hf0K
  have hπs := hπ.1
  have hπi := hπ.2
  let S : Subrepresentation (ρ) :=
    ⟨GlobalTheory.FinZeta.GLSeries.cyc (ρ) f0, by
      intro g u hu
      exact GlobalTheory.FinZeta.GLSeries.cyc_stable _ f0 g u hu⟩
  have hqi : ∀ g (y : S.toSubmodule), q (S.toRepresentation g y) = π g (q y) := fun g y => hq g y
  let qI : S.toRepresentation.IntertwiningMap π :=
    { toLinearMap := q, isIntertwining' := fun g => LinearMap.ext fun y => hqi g y }
  have hqs : Function.Surjective q := by
    let T : Subrepresentation π := ⟨LinearMap.range q, by
      intro g u hu
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hu
      exact LinearMap.mem_range.2 ⟨_, hq g y⟩⟩
    haveI : IsSimpleOrder (Subrepresentation π) := hπi
    rcases eq_bot_or_eq_top T with hT | hT
    · exfalso
      have hm : q ⟨f0, GlobalTheory.FinZeta.GLSeries.self_mem_cyc _ f0⟩ ∈ T.toSubmodule := LinearMap.mem_range_self q _
      rw [hT] at hm
      exact hq0 ((Submodule.mem_bot ℂ).1 hm)
    · intro z
      have hz : z ∈ T.toSubmodule := by
        rw [hT]
        exact Submodule.mem_top
      obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hz
      exact ⟨y, hy⟩
  have hSs : IsSmooth S.toRepresentation := fun y => by
    refine (congrArg IsOpen ?_).mpr (hρs y.1)
    ext g
    exact Subtype.ext_iff
  let P : SmIrr (GL (Fin n) (w.adicCompletion E)) := ⟨W, π, hπs, hπi⟩
  have hy0K : q ⟨f0, GlobalTheory.FinZeta.GLSeries.self_mem_cyc _ f0⟩ ∈ fixed π (GlobalTheory.LFun.KGL w n) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => by
      rw [← hq]
      congr 1
      exact Subtype.ext (GlobalTheory.LGrp.mem_fixed.1 hf0K k hk)
  have hsph : GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w n) := (Submodule.ne_bot_iff _).2 ⟨_, hy0K, hq0⟩
  refine ⟨P, ⟨S, qI, fun z => hqs z⟩, hsph, hsph, fun x hx hx0 => ?_⟩
  have hx' : x ∈ (fixed S.toRepresentation (GlobalTheory.LFun.KGL w n)).map qI.toLinearMap := by
    rw [GlobalTheory.LocGL.map_fixed_of_surjective hSs hKc (f := qI) fun z => hqs z]
    exact hx
  obtain ⟨u, hu, hux⟩ := Submodule.mem_map.1 hx'
  have hqu : q u = x := hux
  have hu0 : u ≠ 0 := fun e => hx0 (by rw [← hqu, e, map_zero])
  have huK : u.1 ∈ fixed (ρ) (GlobalTheory.LFun.KGL w n) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hu k hk)
  have hu1 : GlobalTheory.LFun.IsSatVecGL w (ρ) u.1 B :=
    hsat _ huK fun e => hu0 (Subtype.ext e)
  have hu2 : GlobalTheory.LFun.IsSatVecGL w S.toRepresentation u B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := ρ) S.toSubmodule.subtype (fun _ _ => rfl) Subtype.val_injective hu1
  have hu3 : GlobalTheory.LFun.IsSatVecGL w π (q u) B :=
    hu2.map (ρ' := π) q (fun g y => hqi g y) (by rw [hqu]; exact hx0)
  rw [hqu] at hu3
  exact hu3

theorem unram_component {c : ℕ} {N : Fin c → ℕ} (h : ∑ i, N i = n) (w : HeightOneSpectrum (𝓞 E))
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))) (B : Fin c → Multiset ℂˣ)
    (hB : ∀ i, GlobalTheory.LGrp.IsSpherical (σ i).ρ (GlobalTheory.LFun.KGL w (N i)) ∧ GlobalTheory.LFun.HasSatGL w (σ i).ρ (B i)) :
    ∃ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd h w σ) ∧
      GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w n) ∧ GlobalTheory.LFun.HasSatGL w P.ρ (∑ i, B i) := by
  classical
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have hKO : ∀ m, GlobalTheory.LFun.KGL w m = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin m) :=
    fun m => (GlobalTheory.SmGL.SphCompletion.KO_completion w m).symm

  have hv : ∀ i, ∃ v ∈ fixed (σ i).ρ (GlobalTheory.LFun.KGL w (N i)), v ≠ 0 := fun i =>
    (Submodule.ne_bot_iff _).1 (hB i).1
  choose v hvK hv0 using hv

  obtain ⟨f0, hf0, hf01⟩ := GlobalTheory.SatInd.exists_fixed_apply_one (GlobalTheory.SmGL.stdBlocks N h)
    (ρ := GlobalTheory.SmGL.piTensor fun i => (σ i).ρ) (x := PiTensorProduct.tprod ℂ v) fun g hg => by
      rw [GlobalTheory.SmGL.piTensor_tprod]
      congr 1
      funext a
      exact GlobalTheory.LGrp.mem_fixed.1 (hvK a) (g a) (by rw [hKO]; exact hg a)
  have hf0K : f0 ∈ fixed (locProd h w σ) (GlobalTheory.LFun.KGL w n) := by
    rw [hKO]
    exact hf0
  have hf0ne : f0 ≠ 0 := by
    rintro rfl
    exact unramB_tprod_ne_zero v hv0 hf01.symm

  have hsat : ∀ f ∈ fixed (locProd h w σ) (GlobalTheory.LFun.KGL w n), f ≠ 0 →
      GlobalTheory.LFun.IsSatVecGL w (locProd h w σ) f (∑ i, B i) := by
    intro f hf hf0
    obtain ⟨S, hS, hfS⟩ := GlobalTheory.SatInd.exists_sat_multiProd h (fun a => (σ a).smooth) (fun a => (σ a).irred) hf hf0
    have hSB : S = B := funext fun a => (hS a).unique (hB a).2
    rw [← hSB]
    exact hfS
  exact unramB_irr_quot w (locProd h w σ) (GlobalTheory.SmGL.isSmooth_parInd _ _) hf0ne hf0K _ hsat

end GlobalTheory.PfBCI

end
