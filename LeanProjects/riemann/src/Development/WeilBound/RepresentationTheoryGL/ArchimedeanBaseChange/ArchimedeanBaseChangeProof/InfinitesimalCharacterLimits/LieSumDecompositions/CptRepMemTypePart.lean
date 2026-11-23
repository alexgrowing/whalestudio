import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.GrowPHolds
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PrHolds

noncomputable section

open NumberField MeasureTheory ComplexConjugate
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CapOrth GlobalTheory.LevelTypeProj GlobalTheory.PRep
  GlobalTheory.CuspRep.LocEx PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PrAdm

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Alg

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

section Hilb

variable {W : Submodule ℂ (Sm E N)} (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) (Measure.haar : Measure (GA E N)) φ.1)

theorem inner_cls_eq_pr {x y : Sm E N} (hx : x ∈ W) (hy : y ∈ W) :
    inner ℂ (cls h x) (cls h y) = pr y.1 x.1 := by
  rw [cls_mk h hx, cls_mk h hy]
  exact MemL2Quotient.inner_toL2_eq_theta_pairing (h y hy) (h x hx)

theorem rep_unique (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) {S : Submodule ℂ (Sm E N)} (hS : S ≤ W) {a b : Sm E N}
    (ha : a ∈ S) (hb : b ∈ S) (e : ∀ u ∈ S, inner ℂ (cls h u) (cls h a) = inner ℂ (cls h u) (cls h b)) : a = b := by
  have hm : a - b ∈ S := S.sub_mem ha hb
  have h0 : inner ℂ (cls h (a - b)) (cls h (a - b)) = 0 := by
    rw [cls_sub h (hS ha) (hS hb), inner_sub_right, ← cls_sub h (hS ha) (hS hb), e _ hm, sub_self]
  exact sub_eq_zero.1 (hinj _ (hS hm) (inner_self_eq_zero.1 h0))

theorem exists_rep (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) (S : Submodule ℂ (Sm E N)) [FiniteDimensional ℂ S]
    (hS : S ≤ W) (f : Sm E N → ℂ) (hadd : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x + f y)
    (hsmul : ∀ (c : ℂ), ∀ x ∈ S, f (c • x) = conj c * f x) :
    ∃ a ∈ S, ∀ u ∈ S, f u = inner ℂ (cls h u) (cls h a) := by
  let T : S →ₗ[ℂ] L2 (latticeGL E N) (Measure.haar : Measure (GA E N)) :=
    (toL2ₗ _ W h).comp (Submodule.inclusion hS)
  have hT : Function.Injective T := (injective_iff_map_eq_zero _).2 fun x e => by
    have e' : cls h x.1 = 0 := by rw [cls_mk h (hS x.2)]; exact e
    exact Subtype.ext (hinj _ (hS x.2) e')
  have hTc : ∀ x : S, T x = cls h x.1 := fun x => (cls_mk h (hS x.2)).symm
  let e := LinearEquiv.ofInjective T hT
  have : FiniteDimensional ℂ (LinearMap.range T) := LinearEquiv.finiteDimensional e
  have : CompleteSpace (LinearMap.range T) := FiniteDimensional.complete ℂ _
  let g : LinearMap.range T →ₗ[ℂ] ℂ :=
    { toFun := fun m => conj (f (e.symm m).1)
      map_add' := fun m m' => by
        rw [map_add, Submodule.coe_add, hadd _ (e.symm m).2 _ (e.symm m').2, map_add]
      map_smul' := fun c m => by
        rw [map_smul, Submodule.coe_smul, hsmul c _ (e.symm m).2, map_mul, Complex.conj_conj]
        rfl }
  set t := (InnerProductSpace.toDual ℂ (LinearMap.range T)).symm (LinearMap.toContinuousLinearMap g) with ht
  refine ⟨(e.symm t).1, (e.symm t).2, fun u hu => ?_⟩
  have h1 : cls h (e.symm t).1 = (t : L2 (latticeGL E N) (Measure.haar : Measure (GA E N))) := by
    rw [← hTc]
    exact congrArg Subtype.val (e.apply_symm_apply t)
  have h2 : e.symm ⟨cls h u, ⟨u, hu⟩, hTc ⟨u, hu⟩⟩ = ⟨u, hu⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (hTc ⟨u, hu⟩).symm
  have h3 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := LinearMap.range T)
    (x := (⟨cls h u, ⟨u, hu⟩, hTc ⟨u, hu⟩⟩ : LinearMap.range T)) (y := LinearMap.toContinuousLinearMap g)
  rw [← ht] at h3
  change inner ℂ (t : L2 (latticeGL E N) (Measure.haar : Measure (GA E N))) (cls h u) = conj (f (e.symm _).1) at h3
  rw [h2] at h3
  rw [h1, ← inner_conj_symm, h3, Complex.conj_conj]

end Hilb

theorem coeffSpan_rt {K Y : Type} [Group K] [AddCommGroup Y] [Module ℂ Y] (ρ : Representation ℂ K Y)
    {f : K → ℂ} (hf : f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) (k₀ : K) :
    (fun k => f (k * k₀)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨ℓ, w, rfl⟩ := hf
    refine Submodule.subset_span ⟨ℓ, ρ k₀ w, ?_⟩
    funext k
    show ℓ (ρ (k * k₀) w) = _
    rw [map_mul, Module.End.mul_apply]
  | zero => exact zero_mem _
  | add f g _ _ hf hg => exact add_mem hf hg
  | smul c f _ hf => exact Submodule.smul_mem _ c hf

theorem cptRep_mem_typePart {L : Subgroup (GL (Fin N) (Af E))} {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (Kinf E N) Y} {f : Sm E N} (hf : f ∈ typePart L ρ) (k : Kinf E N) :
    cptRep E N k f ∈ typePart L ρ := by
  refine ⟨fun l hl => by rw [finRep_cptRep, hf.1 l hl], fun g => ?_⟩
  have e : (fun k' : Kinf E N => (cptRep E N k' (cptRep E N k f)).1 g) =
      fun k' => (fun k'' : Kinf E N => (cptRep E N k'' f).1 g) (k' * k) := by
    funext k'
    rw [← Module.End.mul_apply, ← map_mul]
  rw [e]
  exact coeffSpan_rt ρ (hf.2 g) k

section Rep

variable [(Measure.haar : Measure (GA E N)).IsMulRightInvariant] {W : Submodule ℂ (Sm E N)}
  (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) (Measure.haar : Measure (GA E N)) φ.1)

theorem rep_rt (h2 : PairRt) {g : GA E N} (hg : ∀ φ ∈ W, rt E N g φ ∈ W) (hg' : ∀ φ ∈ W, rt E N g⁻¹ φ ∈ W)
    {S : Submodule ℂ (Sm E N)} (hSW : S ≤ W) (hS' : ∀ s ∈ S, rt E N g⁻¹ s ∈ S) {χ : Sm E N}
    (hχ : ∀ γ ∈ latticeGL E N, ∀ y, χ.1 (γ * y) = χ.1 y)
    (hSl : ∀ s ∈ S, ∀ γ ∈ latticeGL E N, ∀ y, s.1 (γ * y) = s.1 y) {p : Sm E N} (hp : p ∈ W)
    (hrep : ∀ s ∈ S, pr χ.1 s.1 = inner ℂ (cls h s) (cls h p)) :
    ∀ s ∈ S, pr (rt E N g χ).1 s.1 = inner ℂ (cls h s) (cls h (rt E N g p)) := by
  intro s hs
  have e1 : pr (rt E N g χ).1 s.1 = pr χ.1 (rt E N g⁻¹ s).1 := h2 E N g χ.1 s.1 hχ (hSl s hs)
  rw [e1, hrep _ (hS' s hs)]
  have e2 := PrSt.inner_rt h hg hg' hp (hSW hs)
  calc inner ℂ (cls h (rt E N g⁻¹ s)) (cls h p) = conj (inner ℂ (cls h p) (cls h (rt E N g⁻¹ s))) :=
        (inner_conj_symm _ _).symm
    _ = conj (inner ℂ (cls h (rt E N g p)) (cls h s)) := by rw [e2]
    _ = inner ℂ (cls h s) (cls h (rt E N g p)) := inner_conj_symm _ _

theorem rep_mem_typePart (h1 : PairLin) (h2 : PairRt) (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) (hW : IsStable W)
    (hWQ : ∀ s ∈ W, GrowQ s.1) {U : Submodule ℂ (Sm E N)} (hU : IsStable U) (hUP : ∀ χ ∈ U, GrowP χ.1)
    {χ : Sm E N} (hχ : χ ∈ U) [FiniteDimensional ℂ (orbSpan χ)] {L : Subgroup (GL (Fin N) (Af E))} {Y : Type}
    [AddCommGroup Y] [Module ℂ Y] {ρ : Representation ℂ (Kinf E N) Y} (hχT : χ ∈ typePart L ρ)
    (S : Submodule ℂ (Sm E N)) [FiniteDimensional ℂ S] (hSW : S ≤ W)
    (hSL : ∀ l ∈ L, ∀ s ∈ S, finRep E N l s ∈ S) (hSK : ∀ k, ∀ s ∈ S, cptRep E N k s ∈ S) {p : Sm E N}
    (hp : p ∈ S) (hrep : ∀ s ∈ S, pr χ.1 s.1 = inner ℂ (cls h s) (cls h p)) : p ∈ typePart L ρ := by
  have hSl : ∀ s ∈ S, ∀ γ ∈ latticeGL E N, ∀ y, s.1 (γ * y) = s.1 y := fun s hs => (hWQ s (hSW hs)).2.1
  have hex : ∀ χ' ∈ U, ∃ a ∈ S, ∀ s ∈ S, pr χ'.1 s.1 = inner ℂ (cls h s) (cls h a) := fun χ' hχ' =>
    exists_rep h hinj S hSW (fun s => pr χ'.1 s.1)
      (fun x hx y hy => ((h1 E N).2 χ'.1 x.1 y.1 1 (hUP χ' hχ') (hWQ x (hSW hx)) (hWQ y (hSW hy))).1)
      (fun c x hx => ((h1 E N).2 χ'.1 x.1 x.1 c (hUP χ' hχ') (hWQ x (hSW hx)) (hWQ x (hSW hx))).2)
  refine ⟨fun l hl => ?_, fun x => ?_⟩
  · have hg : ∀ φ ∈ W, rt E N (finGL E N l) φ ∈ W := fun φ hφ => hW (.fin l) φ hφ
    have hg' : ∀ φ ∈ W, rt E N (finGL E N l)⁻¹ φ ∈ W := fun φ hφ => by
      rw [← map_inv]; exact hW (.fin l⁻¹) φ hφ
    have hS' : ∀ s ∈ S, rt E N (finGL E N l)⁻¹ s ∈ S := fun s hs => by
      rw [← map_inv]; exact hSL l⁻¹ (L.inv_mem hl) s hs
    have ht := rep_rt h h2 hg hg' hSW hS' (hUP χ hχ).2.1 hSl (hSW hp) hrep
    refine rep_unique h hinj hSW (hSL l hl p hp) hp fun s hs => ?_
    have e : rt E N (finGL E N l) χ = χ := hχT.1 l hl
    have e2 := ht s hs
    rw [e] at e2
    rw [← hrep s hs, e2]
    rfl
  · let O := orbSpan χ
    have hOU : O ≤ U := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hU (.cpt k) χ hχ)
    choose! Q hQS hQ using hex
    let Φ : O →ₗ[ℂ] Sm E N :=
      { toFun := fun χ' => Q χ'.1
        map_add' := fun a b => by
          refine rep_unique h hinj hSW (hQS _ (hOU (a + b).2))
            (S.add_mem (hQS _ (hOU a.2)) (hQS _ (hOU b.2))) fun s hs => ?_
          rw [← hQ (a + b : O).1 (hOU (a + b).2) s hs, cls_add h (hSW (hQS _ (hOU a.2))) (hSW (hQS _ (hOU b.2))),
            inner_add_right, ← hQ _ (hOU a.2) s hs, ← hQ _ (hOU b.2) s hs]
          exact ((h1 E N).1 a.1.1 b.1.1 s.1 1 (hUP _ (hOU a.2)) (hUP _ (hOU b.2)) (hWQ s (hSW hs))).1
        map_smul' := fun c a => by
          refine rep_unique h hinj hSW (hQS _ (hOU (c • a).2)) (S.smul_mem c (hQS _ (hOU a.2)))
            fun s hs => ?_
          rw [← hQ (c • a : O).1 (hOU (c • a).2) s hs, RingHom.id_apply, cls_smul h c (hSW (hQS _ (hOU a.2))),
            inner_smul_right, ← hQ _ (hOU a.2) s hs]
          exact ((h1 E N).1 a.1.1 a.1.1 s.1 c (hUP _ (hOU a.2)) (hUP _ (hOU a.2)) (hWQ s (hSW hs))).2 }
    have hΦ : ∀ k, cptRep E N k p = Φ ⟨cptRep E N k χ, Submodule.subset_span ⟨k, rfl⟩⟩ := fun k => by
      have hg : ∀ φ ∈ W, rt E N (infGL E N (Unitary.toUnits k)) φ ∈ W := fun φ hφ => hW (.cpt k) φ hφ
      have hg' : ∀ φ ∈ W, rt E N (infGL E N (Unitary.toUnits k))⁻¹ φ ∈ W := fun φ hφ => by
        rw [← map_inv, ← map_inv]; exact hW (.cpt k⁻¹) φ hφ
      have hS' : ∀ s ∈ S, rt E N (infGL E N (Unitary.toUnits k))⁻¹ s ∈ S := fun s hs => by
        rw [← map_inv, ← map_inv]; exact hSK k⁻¹ s hs
      have ht := rep_rt h h2 hg hg' hSW hS' (hUP χ hχ).2.1 hSl (hSW hp) hrep
      have hkU : cptRep E N k χ ∈ U := hU (.cpt k) χ hχ
      refine rep_unique h hinj hSW (hSK k p hp) (hQS _ hkU) fun s hs => ?_
      show _ = inner ℂ (cls h s) (cls h (Q (cptRep E N k χ)))
      rw [← hQ _ hkU s hs]
      exact (ht s hs).symm
    let Λ : Module.Dual ℂ O →ₗ[ℂ] (Kinf E N → ℂ) :=
      { toFun := fun ℓ k => ℓ ⟨cptRep E N k χ, Submodule.subset_span ⟨k, rfl⟩⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    let ev : GA E N → Module.Dual ℂ O := fun y => (LinearMap.proj y).comp ((Sm E N).subtype.comp O.subtype)
    have htop := span_eval_eq_top ev fun w hw => Subtype.ext (Subtype.ext (funext hw))
    have hle : Submodule.span ℂ (Set.range ev) ≤ (GlobalTheory.Published.AutFin.coeffSpan ρ).comap Λ :=
      Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hχT.2 y)
    let ℓ : Module.Dual ℂ O := (LinearMap.proj x).comp ((Sm E N).subtype.comp Φ)
    have hℓ : Λ ℓ ∈ GlobalTheory.Published.AutFin.coeffSpan ρ := hle (htop ▸ Submodule.mem_top)
    convert hℓ using 1
    funext k
    rw [hΦ k]
    rfl

theorem exists_repV (h1 : PairLin) (h2 : PairRt) (hinj : ∀ x ∈ W, cls h x = 0 → x = 0) (hW : IsStable W)
    (hWA : ∀ x ∈ W, IsAutForm x) (hWQ : ∀ s ∈ W, GrowQ s.1) {V : Submodule ℂ (Sm E N)} (hV : IsStable V)
    (hVW : V ≤ W)
    (hVfd : ∀ (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) → ∀ (Y : Type)
      [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Kinf E N) Y),
        GlobalTheory.Published.AutFin.IsContRep ρ → FiniteDimensional ℂ (V ⊓ typePart L ρ : Submodule ℂ (Sm E N)))
    {U : Submodule ℂ (Sm E N)} (hU : IsStable U) (hUA : ∀ χ ∈ U, IsAutForm χ) (hUP : ∀ χ ∈ U, GrowP χ.1)
    {χ : Sm E N} (hχ : χ ∈ U) : ∃ a ∈ V, ∀ u ∈ V, pr χ.1 u.1 = inner ℂ (cls h u) (cls h a) := by
  obtain ⟨L, hLo, hLc, hχT⟩ := exists_type (hUA χ hχ)
  have : FiniteDimensional ℂ (orbSpan χ) := (hUA χ hχ).kfin
  have hρ := isContRep_sub (orbSpan χ) (orbSpan_stable χ)
  set ρ := sub (cptRep E N) (orbSpan χ) (orbSpan_stable χ)
  set F : Submodule ℂ (Sm E N) := V ⊓ typePart L ρ with hFdef
  have : FiniteDimensional ℂ F := hVfd L hLo _ ρ hρ
  have hFW : F ≤ W := inf_le_left.trans hVW
  have hadd : ∀ (S : Submodule ℂ (Sm E N)), S ≤ W → ∀ x ∈ S, ∀ y ∈ S,
      pr χ.1 (x + y).1 = pr χ.1 x.1 + pr χ.1 y.1 :=
    fun S hS x hx y hy => ((h1 E N).2 χ.1 x.1 y.1 1 (hUP χ hχ) (hWQ x (hS hx)) (hWQ y (hS hy))).1
  have hsm : ∀ (S : Submodule ℂ (Sm E N)), S ≤ W → ∀ (c : ℂ), ∀ x ∈ S, pr χ.1 (c • x).1 = conj c * pr χ.1 x.1 :=
    fun S hS c x hx => ((h1 E N).2 χ.1 x.1 x.1 c (hUP χ hχ) (hWQ x (hS hx)) (hWQ x (hS hx))).2
  obtain ⟨a, haF, ha⟩ := exists_rep h hinj F hFW (fun s => pr χ.1 s.1) (hadd F hFW) (hsm F hFW)
  refine ⟨a, haF.1, fun u hu => ?_⟩
  have : FiniteDimensional ℂ (orbitSpan L u) := orbitSpan_finiteDimensional L hLc u (hWA u (hVW hu))
  set S' : Submodule ℂ (Sm E N) := orbitSpan L u ⊔ F with hS'def
  have hS'V : S' ≤ V := sup_le (orbitSpan_le hV L hu) inf_le_left
  have hS'W : S' ≤ W := hS'V.trans hVW
  have hSL : ∀ l ∈ L, ∀ s ∈ S', finRep E N l s ∈ S' := fun l hl s hs => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hs
    rw [map_add]
    refine add_mem (Submodule.mem_sup_left (finRep_mem_orbitSpan hl hy)) (Submodule.mem_sup_right ?_)
    rw [hz.2.1 l hl]
    exact hz
  have hSK : ∀ k, ∀ s ∈ S', cptRep E N k s ∈ S' := fun k s hs => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hs
    rw [map_add]
    exact add_mem (Submodule.mem_sup_left (cptRep_mem_orbitSpan k hy))
      (Submodule.mem_sup_right ⟨hV (.cpt k) z hz.1, cptRep_mem_typePart hz.2 k⟩)
  obtain ⟨p, hpS, hp⟩ := exists_rep h hinj S' hS'W (fun s => pr χ.1 s.1) (hadd S' hS'W) (hsm S' hS'W)
  have hpT := rep_mem_typePart h h1 h2 hinj hW hWQ hU hUP hχ hχT S' hS'W hSL hSK hpS hp
  have hpF : p ∈ F := ⟨hS'V hpS, hpT⟩
  have hpa : p = a := rep_unique h hinj hFW hpF haF fun s hs => by
    rw [← hp s (Submodule.mem_sup_right hs), ← ha s hs]
  rw [hp u (Submodule.mem_sup_left (mem_orbitSpan_self L u)), hpa]

end Rep

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux.Alg

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

open Alg in

theorem core_of (h1 : PairLin) (h2 : PairRt) (h3 : PairLie) (h4 : GrowQHolds) : Core := by
  intro E _ _ _ N U hU hUA hUP φ hφU hφA hφ0
  have : (Measure.haar : Measure (GA E N)).IsMulRightInvariant := GlobalTheory.CovolGL.isMulRightInvariant E N _
  have hF := PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL
  have hW : IsStable (A2 E N) := PrSt.isStable_square_integrable_forms hF
  have hA : ∀ x ∈ A2 E N, IsAutForm x := fun x hx => (PrSt.mem_square_integrable_forms hx).1
  have h : ∀ x ∈ A2 E N, MemL2Quotient (latticeGL E N) (Measure.haar : Measure (GA E N)) x.1 := fun x hx =>
    memL2_of_isAutForm (PrSt.mem_square_integrable_forms hx).1 (PrSt.mem_square_integrable_forms hx).2
  have hF2 := toL2ₗ_injective h fun x hx => ContAut.continuous_of_isOpen_stab E N x (hA x hx).level
  have hinj : ∀ x ∈ A2 E N, cls h x = 0 → x = 0 := fun x hx e => by
    rw [cls_mk h hx] at e
    exact congrArg Subtype.val (hF2 (e.trans (map_zero _).symm))
  have hadj := fun o => PrSt.exists_adj h hW hA o
  obtain ⟨V, hVst, hVA, hV0, hirr, v, hvV, hvφ⟩ := PrIrr.exists_irr h hW hA hinj hadj hφA hφ0
  have hVW : V ≤ A2 E N := hVA.trans (admissible_span_le _ φ)
  have hWQ : ∀ s ∈ A2 E N, GrowQ s.1 := fun s hs => h4 E N s (PrSt.mem_square_integrable_forms hs).1 (PrSt.mem_square_integrable_forms hs).2
  have hVfd : ∀ (L : Subgroup (GL (Fin N) (Af E))), IsOpen (L : Set (GL (Fin N) (Af E))) → ∀ (Y : Type)
      [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (ρ : Representation ℂ (Kinf E N) Y),
        GlobalTheory.Published.AutFin.IsContRep ρ → FiniteDimensional ℂ (V ⊓ typePart L ρ : Submodule ℂ (Sm E N)) := by
    intro L hLo Y _ _ _ ρ hρ
    have := finiteDimensional_admissible_isotypic hA (hA φ hφA) hLo ρ hρ
    exact Submodule.finiteDimensional_of_le (inf_le_inf_right _ hVA)
  have hrep : ∀ χ ∈ U, ∃ a ∈ V, ∀ u ∈ V, pr χ.1 u.1 = inner ℂ (cls h u) (cls h a) := fun χ hχ =>
    exists_repV h h1 h2 hinj hW hA hWQ hVst hVW hVfd hU hUA hUP hχ
  choose! P hPV hP using hrep
  let pU : U →ₗ[ℂ] Sm E N :=
    { toFun := fun χ => P χ.1
      map_add' := fun x y => by
        refine rep_unique h hinj hVW (hPV _ (x + y).2) (V.add_mem (hPV _ x.2) (hPV _ y.2)) fun u hu => ?_
        rw [← hP (x + y : U).1 (x + y).2 u hu, cls_add h (hVW (hPV _ x.2)) (hVW (hPV _ y.2)), inner_add_right,
          ← hP _ x.2 u hu, ← hP _ y.2 u hu]
        exact ((h1 E N).1 x.1.1 y.1.1 u.1 1 (hUP _ x.2) (hUP _ y.2) (hWQ u (hVW hu))).1
      map_smul' := fun c x => by
        refine rep_unique h hinj hVW (hPV _ (c • x).2) (V.smul_mem c (hPV _ x.2)) fun u hu => ?_
        rw [← hP (c • x : U).1 (c • x).2 u hu, RingHom.id_apply, cls_smul h c (hVW (hPV _ x.2)),
          inner_smul_right, ← hP _ x.2 u hu]
        exact ((h1 E N).1 x.1.1 x.1.1 u.1 c (hUP _ x.2) (hUP _ x.2) (hWQ u (hVW hu))).2 }
  obtain ⟨p, hp⟩ := LinearMap.exists_extend pU
  have hpU : ∀ χ ∈ U, p χ = P χ := fun χ hχ => LinearMap.congr_fun hp ⟨χ, hχ⟩
  refine ⟨V, p, ⟨fun x hx => hA x (hVW hx), fun x hx => (PrSt.mem_square_integrable_forms (hVW hx)).2, hVst, hV0, hirr⟩,
    fun χ hχ => by rw [hpU χ hχ]; exact hPV χ hχ, fun o χ hχ => ?_, ?_⟩
  · rw [hpU _ (hU o χ hχ), hpU χ hχ]
    refine rep_unique h hinj hVW (hPV _ (hU o χ hχ)) (hVst o _ (hPV χ hχ)) fun u hu => ?_
    rw [← hP _ (hU o χ hχ) u hu]
    have hχl := (hUP χ hχ).2.1
    have hVl : ∀ s ∈ V, ∀ γ ∈ latticeGL E N, ∀ y, s.1 (γ * y) = s.1 y := fun s hs => (hWQ s (hVW hs)).2.1
    cases o with
    | fin k =>
      have hg : ∀ x ∈ A2 E N, rt E N (finGL E N k) x ∈ A2 E N := fun x hx => hW (.fin k) x hx
      have hg' : ∀ x ∈ A2 E N, rt E N (finGL E N k)⁻¹ x ∈ A2 E N := fun x hx => by
        rw [← map_inv]; exact hW (.fin k⁻¹) x hx
      have hS' : ∀ s ∈ V, rt E N (finGL E N k)⁻¹ s ∈ V := fun s hs => by
        rw [← map_inv]; exact hVst (.fin k⁻¹) s hs
      exact rep_rt h h2 hg hg' hVW hS' hχl hVl (hVW (hPV χ hχ)) (hP χ hχ) u hu
    | cpt k =>
      have hg : ∀ x ∈ A2 E N, rt E N (infGL E N (Unitary.toUnits k)) x ∈ A2 E N := fun x hx => hW (.cpt k) x hx
      have hg' : ∀ x ∈ A2 E N, rt E N (infGL E N (Unitary.toUnits k))⁻¹ x ∈ A2 E N := fun x hx => by
        rw [← map_inv, ← map_inv]; exact hW (.cpt k⁻¹) x hx
      have hS' : ∀ s ∈ V, rt E N (infGL E N (Unitary.toUnits k))⁻¹ s ∈ V := fun s hs => by
        rw [← map_inv, ← map_inv]; exact hVst (.cpt k⁻¹) s hs
      exact rep_rt h h2 hg hg' hVW hS' hχl hVl (hVW (hPV χ hχ)) (hP χ hχ) u hu
    | lie X =>
      have e1 := h3 E N X χ u (hUP χ hχ) (hUP _ (hU (.lie X) χ hχ)) (hWQ u (hVW hu))
        (hWQ _ (hW (.lie X) u (hVW hu)))
      rw [e1, hP χ hχ _ (hVst (.lie X) u hu)]
      have e2 := GlobalTheory.LieSkew.lie_skew E N (Measure.haar : Measure (GA E N)) (A2 E N) h hW hA X ⟨u, hVW hu⟩
        ⟨P χ, hVW (hPV χ hχ)⟩
      rw [cls_mk h (hW (.lie X) u (hVW hu)), cls_mk h (hVW (hPV χ hχ)), cls_mk h (hVW hu),
        cls_mk h (hW (.lie X) (P χ) (hVW (hPV χ hχ)))]
      rw [e2, neg_neg]
  · rw [hpU φ hφU]
    intro e
    have h0 := hP φ hφU v hvV
    rw [e, show (0 : Sm E N) = (0 : ℂ) • (0 : Sm E N) by simp, cls_smul h 0 (A2 E N).zero_mem, zero_smul,
      inner_zero_right] at h0
    have h5 := inner_cls_eq_pr h (hVW hvV) hφA
    apply hvφ
    rw [← inner_conj_symm, h5, h0, map_zero]

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.Leaf2Aux

end
