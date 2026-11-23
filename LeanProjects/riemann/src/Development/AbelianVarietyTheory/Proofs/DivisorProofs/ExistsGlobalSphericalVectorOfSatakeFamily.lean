import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFixedOfMemISup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalTranslationCompCommutingOperator

noncomputable section

open NumberField IsDedekindDomain Matrix Filter

namespace GlobalTheory.JSW.SphVec

open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.LFun

theorem map_mem_twKer {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {K : Subgroup G}
    (S : V →ₗ[ℂ] W) (hS : ∀ h v, S (ρ h v) = σ h (S v)) {v : V} (hv : v ∈ twKer ρ K 1) : S v ∈ twKer σ K 1 := by
  have h : (twKer ρ K 1).map S ≤ twKer σ K 1 := by
    rw [twKer, Submodule.map_span_le]
    rintro _ ⟨n, u, rfl⟩
    exact Submodule.subset_span ⟨n, S u, by simp [hS]⟩
  exact h ⟨v, hv, rfl⟩

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem exists_fixed_mem (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E))
    (hS : GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) (U : Submodule ℂ π.V)
    (hU : ∀ g, ∀ v ∈ U, π.locRep w g v ∈ U) {y : π.V} (hy : y ∈ U) (hy0 : y ≠ 0) :
    ∃ x ∈ U, x ≠ 0 ∧ ∀ k ∈ KGL w a, π.locRep w k x = x := by
  have hK : IsCompact ((KGL w a : Subgroup _) : Set (GL (Fin a) (w.adicCompletion E))) :=
    (GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a).2
  have hsm : IsSmooth (π.locRep w) := π.isSmooth_locRep w
  have hsU : IsSmooth (GlobalTheory.PRep.sub (π.locRep w) U hU) := fun v => by
    convert hsm v.1 using 1
    ext g
    exact Subtype.ext_iff
  by_contra hne
  have hbot : fixed (GlobalTheory.PRep.sub (π.locRep w) U hU) (KGL w a) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra h0
    exact hne ⟨v.1, v.2, fun h => h0 (Subtype.ext h), fun k hk =>
      congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hv k hk)⟩
  have htop := (GlobalTheory.LocGL.isCompl_fixed_twKer hsU hK).sup_eq_top
  rw [hbot, bot_sup_eq] at htop
  have hall : ∀ g, π.locRep w g y ∈ twKer (π.locRep w) (KGL w a) 1 := fun g =>
    map_mem_twKer (ρ := GlobalTheory.PRep.sub (π.locRep w) U hU) U.subtype (fun _ _ => rfl)
      (v := ⟨_, hU g y hy⟩) (htop ▸ Submodule.mem_top)
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1 hS
  let Wl : Submodule ℂ π.V := ⨅ g, (twKer (π.locRep w) (KGL w a) 1).comap (π.locRep w g)
  have memWl : ∀ v, v ∈ Wl ↔ ∀ g, π.locRep w g v ∈ twKer (π.locRep w) (KGL w a) 1 := fun v => by
    simp [Wl, Submodule.mem_iInf]
  have stab : GlobalTheory.CuspRep.IsStable (Wl.map π.V.subtype) := by
    rintro o _ ⟨v, hv, rfl⟩
    obtain ⟨g, S, hS, ho⟩ := GlobalTheory.LocFactor.op_eq_locRep_comp π w o
    have hv' := (memWl v).1 hv
    refine ⟨π.op o v, (memWl _).2 fun h => ?_, rfl⟩
    rw [ho, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul]
    have e := LinearMap.congr_fun (hS (h * g)) v
    simp only [LinearMap.comp_apply] at e
    rw [← e]
    exact map_mem_twKer S (fun h v => LinearMap.congr_fun (hS h) v) (hv' (h * g))
  rcases π.irred _ (Submodule.map_subtype_le _ _) stab with h | h
  · have h1 : (y : Sm E a) ∈ Wl.map π.V.subtype := ⟨y, (memWl y).2 hall, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    exact hy0 (Subtype.ext h1)
  · have h1 : (x : Sm E a) ∈ Wl.map π.V.subtype := by rw [h]; exact x.2
    obtain ⟨x', hx', e⟩ := h1
    obtain rfl : x' = x := Subtype.ext e
    have h2 := (memWl x').1 hx' 1
    rw [map_one, Module.End.one_apply] at h2
    exact hx0 (Submodule.disjoint_def.1 (GlobalTheory.LocGL.isCompl_fixed_twKer hsm hK).disjoint x' hx h2)

theorem locRep_comm (π : CuspSub E a) {v w : HeightOneSpectrum (𝓞 E)} (h : w ≠ v)
    (k : GL (Fin a) (v.adicCompletion E)) (g : GL (Fin a) (w.adicCompletion E)) (x : π.V) :
    π.locRep v k (π.locRep w g x) = π.locRep w g (π.locRep v k x) := by
  simp only [CuspSub.locRep, MonoidHom.comp_apply]
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul,
    LocSph.comm_locGL w _ (pLoc_locGL_of_ne h k)]

theorem exists_fixed_union (π : CuspSub E a) (T : Set (HeightOneSpectrum (𝓞 E))) {y : π.V} (hy0 : y ≠ 0)
    (hy : ∀ v ∈ T, ∀ k ∈ KGL v a, π.locRep v k y = y) (F : Finset (HeightOneSpectrum (𝓞 E)))
    (hF : ∀ w ∈ F, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) :
    ∃ x : π.V, x ≠ 0 ∧ ∀ v, v ∈ T ∨ v ∈ F → ∀ k ∈ KGL v a, π.locRep v k x = x := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨y, hy0, fun v hv => hy v (by simpa using hv)⟩
  | insert w F _ ih =>
    obtain ⟨x, hx0, hx⟩ := ih fun v hv => hF v (Finset.mem_insert_of_mem hv)
    let U : Submodule ℂ π.V := ⨅ v : {v // (v ∈ T ∨ v ∈ F) ∧ w ≠ v}, fixed (π.locRep v.1) (KGL v.1 a)
    have memU : ∀ z, z ∈ U ↔ ∀ v, (v ∈ T ∨ v ∈ F) → w ≠ v → ∀ k ∈ KGL v a, π.locRep v k z = z := fun z => by
      simp only [U, Submodule.mem_iInf, GlobalTheory.LGrp.mem_fixed, Subtype.forall]
      exact ⟨fun h v h1 h2 => h v ⟨h1, h2⟩, fun h v h1 => h v h1.1 h1.2⟩
    obtain ⟨z, hz, hz0, hzw⟩ := exists_fixed_mem π w (hF w (Finset.mem_insert_self _ _)) U
      (fun g z hz => (memU _).2 fun v hv hne k hk => by
        rw [locRep_comm π hne, (memU z).1 hz v hv hne k hk])
      ((memU x).2 fun v hv _ => hx v hv) hx0
    refine ⟨z, hz0, fun v hv => ?_⟩
    by_cases hne : w = v
    · subst hne; exact hzw
    · refine (memU z).1 hz v (hv.imp_right fun h => ?_) hne
      exact (Finset.mem_insert.1 h).resolve_left fun e => hne e.symm

theorem exists_sphVec_of_isSpherical (π : CuspSub E a) (S : Set (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, GlobalTheory.LGrp.IsSpherical (π.locRep w) (KGL w a)) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ := by
  classical
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have hev := LocSph.eventually_mem ((π.cusp φ hφ).1.level.mem_nhds (by simp))
  rw [Filter.eventually_cofinite] at hev
  obtain ⟨x, hx0, hx⟩ := exists_fixed_union π
    {w | ∀ g : GL (Fin a) (w.adicCompletionIntegers E),
      locGL E a w (GeneralLinearGroup.map (w.adicCompletionIntegers E).subtype g) ∈ {k | finRep E a k φ = φ}}
    (y := ⟨φ, hφ⟩) (fun h => h0 (congrArg Subtype.val h))
    (by rintro v hv _ ⟨g, rfl⟩; exact Subtype.ext (hv g))
    (hev.toFinset.filter (· ∉ S)) (fun w hw => hS w (Finset.mem_filter.1 hw).2)
  refine ⟨x.1, x.2, fun h => hx0 (Subtype.ext h), fun w hw k hk => congrArg Subtype.val (hx w ?_ k hk)⟩
  refine (em _).imp_right fun h => Finset.mem_filter.2 ⟨hev.mem_toFinset.2 h, hw⟩

theorem exists_sphVec (π : CuspSub E a) (S : Finset (HeightOneSpectrum (𝓞 E)))
    (hS : ∀ w ∉ S, ∃ B, HasSatGL w (π.locRep w) B) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec_of_isSpherical π S fun w hw => (hS w hw).elim fun _ h => h.1

theorem exists_sphVec_of_hasSat (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (B : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ)
    (h : ∀ w ∉ S, HasSatGL w (π.locRep w) (B w)) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ w ∉ S, ∀ k ∈ KGL w a, act (.fin (locGL E a w k)) φ = φ :=
  exists_sphVec π S fun w hw => ⟨B w, h w hw⟩

end GlobalTheory.JSW.SphVec
