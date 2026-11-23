import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}

open scoped Classical in

def coef {v : Pl F} (ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)) (l : Fn F n d v →ₗ[ℂ] ℂ) :
    Fn F n d v →ₗ[ℂ] (UA σ W.J → ℂ) where
  toFun φ h := if h ∈ UAt σ W (evFin F v) then l (ω (1, h) φ) else 0
  map_add' φ φ' := by funext h; by_cases hh : h ∈ UAt σ W (evFin F v) <;> simp [hh]
  map_smul' c φ := by funext h; by_cases hh : h ∈ UAt σ W (evFin F v) <;> simp [hh]

section Loc

variable {v : Pl F} {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {l : Fn F n d v →ₗ[ℂ] ℂ}

theorem coef_mem {φ : Fn F n d v} {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) : coef ω l φ h = l (ω (1, h) φ) := by
  simp [coef, hh]

theorem coef_not_mem {φ : Fn F n d v} {h : UA σ W.J} (hh : h ∉ UAt σ W (evFin F v)) : coef ω l φ h = 0 := by
  simp [coef, hh]

variable {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

theorem aug_stable (L : IsLocRep M ψ om v ω ρ) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) :
    augAt om v ≤ (augAt om v).comap (ω (1, h)) := by
  have o1 := one_mem_UAt (σ := σ) X v
  have oW := one_mem_UAt (σ := σ) W v
  conv_lhs => unfold augAt
  rw [Submodule.span_le]
  rintro _ ⟨g, hg, φ, hφ, φ₁, hφ₁, ha, rfl⟩
  rw [(L.acts g hg 1 oW φ hφ φ₁).1 ha]
  have hφh := L.pres 1 o1 h hh φ hφ
  have e1 : ω (1, h) (ω (g, 1) φ) = ω (g, 1) (ω (1, h) φ) := by
    rw [← L.mul 1 o1 h hh g hg 1 oW φ hφ, ← L.mul g hg 1 oW 1 o1 h hh φ hφ]
    simp
  change ω (1, h) (ω (g, 1) φ - φ) ∈ augAt om v
  rw [map_sub, e1]
  exact Submodule.subset_span ⟨g, hg, _, hφh, _, L.pres g hg 1 oW _ hφh, (L.acts g hg 1 oW _ hφh _).2 rfl, rfl⟩

theorem coef_aug (L : IsLocRep M ψ om v ω ρ) (hl : augAt om v ≤ LinearMap.ker l) : augAt om v ≤ LinearMap.ker (coef ω l) := by
  intro z hz
  rw [LinearMap.mem_ker]
  funext h
  by_cases hh : h ∈ UAt σ W (evFin F v)
  · rw [coef_mem hh]; exact hl (aug_stable L hh hz)
  · rw [coef_not_mem hh]; rfl

theorem coef_transl (L : IsLocRep M ψ om v ω ρ) {h : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) {φ : Fn F n d v}
    (hφ : φ ∈ SB _) : coef ω l (ω (1, h) φ) = fun x => coef ω l φ (x * h) := by
  have o1 := one_mem_UAt (σ := σ) X v
  funext x
  by_cases hx : x ∈ UAt σ W (evFin F v)
  · rw [coef_mem hx, coef_mem (mul_mem_UAt hx hh), ← L.mul 1 o1 x hx 1 o1 h hh φ hφ, mul_one]
  · have hxh : x * h ∉ UAt σ W (evFin F v) := fun h' => hx (by
      have := mul_mem_UAt h' (inv_mem_UAt hh); rwa [mul_inv_cancel_right] at this)
    rw [coef_not_mem hx, coef_not_mem hxh]

def transl (Ω : UA σ W.J → ℂ) (v : Pl F) : Submodule ℂ (UA σ W.J → ℂ) :=
  Submodule.span ℂ {f | ∃ h ∈ UAt σ W (evFin F v), f = fun x => Ω (x * h)}

theorem map_coef (L : IsLocRep M ψ om v ω ρ) (V : IsVacSph M om v ω) (hs : M.vac v ∈ SB _) (hl : IsSphForm M om v ω l) :
    (SB _).map (coef ω l) = transl (coef ω l (M.vac v)) v := by
  have o1 := one_mem_UAt (σ := σ) X v
  apply le_antisymm
  · rintro _ ⟨φ, hφ, rfl⟩
    have h1 : augAt om v ≤ (transl (coef ω l (M.vac v)) v).comap (coef ω l) := fun z hz => by
      rw [Submodule.mem_comap, (LinearMap.mem_ker).1 (coef_aug L hl.aug hz)]; exact Submodule.zero_mem _
    have h2 : Submodule.span ℂ {z | ∃ h ∈ UAt σ W (evFin F v), z = ω (1, h) (M.vac v)} ≤
        (transl (coef ω l (M.vac v)) v).comap (coef ω l) := by
      rw [Submodule.span_le]
      rintro _ ⟨h, hh, rfl⟩
      exact Submodule.subset_span ⟨h, hh, coef_transl L hh hs⟩
    exact sup_le h1 h2 (V.gen φ hφ)
  · rw [transl, Submodule.span_le]
    rintro _ ⟨h, hh, rfl⟩
    exact ⟨_, L.pres 1 o1 h hh _ hs, coef_transl L hh hs⟩

theorem coef_vac_one (L : IsLocRep M ψ om v ω ρ) (hs : M.vac v ∈ SB _) (hl : IsSphForm M om v ω l) :
    coef ω l (M.vac v) 1 = 1 := by
  rw [coef_mem (one_mem_UAt W v)]
  have : ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 := rfl
  rw [this, L.one _ hs, hl.one]

theorem reach_vac (L : IsLocRep M ψ om v ω ρ) (V : IsVacSph M om v ω) (hl : IsSphForm M om v ω l) {φ : Fn F n d v}
    (hφ : φ ∈ SB _) (h0 : coef ω l φ ≠ 0) :
    ∃ h ∈ UAt σ W (evFin F v), ∃ (m : ℕ) (k : Fin (m + 1) → UA σ W.J) (c : ℂ), c ≠ 0 ∧
      (∀ i, k i ∈ KAt σ W v) ∧ ∑ i, ω (1, k i) (ω (1, h) φ) - c • M.vac v ∈ augAt om v := by
  have o1 := one_mem_UAt (σ := σ) X v
  obtain ⟨h, hh⟩ : ∃ h, coef ω l φ h ≠ 0 := by
    by_contra hc; exact h0 (funext fun x => by_contra fun hx => hc ⟨x, hx⟩)
  have hU : h ∈ UAt σ W (evFin F v) := by
    by_contra hn; exact hh (coef_not_mem hn)
  rw [coef_mem hU] at hh
  have hψ := L.pres 1 o1 h hU φ hφ
  obtain ⟨m, k, c, hk, hsum⟩ := V.line _ hψ
  refine ⟨h, hU, m, k, c, ?_, hk, hsum⟩
  intro hc0
  have := hl.aug hsum
  rw [LinearMap.mem_ker, map_sub, map_sum, hc0, zero_smul, map_zero, sub_zero] at this
  have e : ∀ i, l (ω (1, k i) (ω (1, h) φ)) = l (ω (1, h) φ) := fun i => hl.inv _ (hk i) _ hψ
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  rcases mul_eq_zero.1 this with h1 | h1
  · exact absurd h1 (by exact_mod_cast Nat.succ_ne_zero m)
  · exact hh h1

end Loc

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {v : Pl F}

theorem finAt_sph {ω ρ ω' ρ'} (L : IsLocRep G.M B.ψ om v ω ρ) (L' : IsLocRep G.M' B.ψ om' v ω' ρ') (hv : v ∉ X.T)
    (hs : G.M.vac v ∈ SB _) (hs' : G.M'.vac v ∈ SB _) (V1 : IsVacSph G.M om v ω) (V2 : IsVacSph G.M' om' v ω')
    {l l'} (hl : IsSphForm G.M om v ω l) (hl' : IsSphForm G.M' om' v ω' l')
    (hΩ : ∀ h ∈ UAt σ G.W (evFin F v), l (ω (1, h) (G.M.vac v)) = l' (ω' (1, h) (G.M'.vac v))) :
    ∃ R, IsFinAt B G X om om' R v := by
  classical
  have o1 := one_mem_UAt (σ := σ) G.V v
  have o1' := one_mem_UAt (σ := σ) G.V' v
  set c := coef ω l with hc
  set c' := coef ω' l' with hc'
  have eΩ : c (G.M.vac v) = c' (G.M'.vac v) := by
    funext x
    by_cases hx : x ∈ UAt σ G.W (evFin F v)
    · rw [hc, hc', coef_mem hx, coef_mem hx]; exact hΩ x hx
    · rw [hc, hc', coef_not_mem hx, coef_not_mem hx]
  set S := transl (c (G.M.vac v)) v with hS
  have mS : (SB _).map c = S := map_coef L V1 hs hl
  have mS' : (SB _).map c' = S := by rw [hS, eΩ]; exact map_coef L' V2 hs' hl'
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective S.subtype S.ker_subtype
  have hπ' : ∀ x (hx : x ∈ S), π x = ⟨x, hx⟩ := fun x hx => LinearMap.congr_fun hπ ⟨x, hx⟩
  have mc : ∀ φ ∈ SB _, c φ ∈ S := fun φ hφ => mS ▸ Submodule.mem_map_of_mem hφ
  have mc' : ∀ φ ∈ SB _, c' φ ∈ S := fun φ hφ => mS' ▸ Submodule.mem_map_of_mem hφ
  have inj : ∀ x ∈ S, ∀ y ∈ S, π x = π y → x = y := fun x hx y hy h => by
    rw [hπ' x hx, hπ' y hy] at h; exact congrArg Subtype.val h
  let R : FinMaps F a a' :=
    { Pi := fun _ => S
      p := fun u => if h : v = u then h ▸ (π ∘ₗ c) else 0
      p' := fun u => if h : v = u then h ▸ (π ∘ₗ c') else 0 }
  have e : R.p v = π ∘ₗ c := dif_pos rfl
  have e' : R.p' v = π ∘ₗ c' := dif_pos rfl
  have hx : ∀ x : S, π x.1 = x := fun x => hπ' x.1 x.2
  have on : ∀ x : S, ∃ φ ∈ SB _, c φ = x := fun x => (mS.symm ▸ x.2 : x.1 ∈ (SB _).map c)
  have on' : ∀ x : S, ∃ φ ∈ SB _, c' φ = x := fun x => (mS'.symm ▸ x.2 : x.1 ∈ (SB _).map c')
  have Ω1 : c (G.M.vac v) 1 = 1 := coef_vac_one L hs hl
  have ΩS : c (G.M.vac v) ∈ S := mc _ hs
  have Ω0 : c (G.M.vac v) ≠ 0 := fun h => by
    have := congrFun h 1; rw [Ω1] at this; exact one_ne_zero this
  have hne : π (c (G.M.vac v)) ≠ 0 := fun h => Ω0 (inj _ ΩS 0 S.zero_mem (h.trans (map_zero π).symm))
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ⟨_, _, hne⟩, ?_, fun _ => ?_, fun _ h => absurd h hv⟩
  · rw [e, eq_top_iff]
    intro x _
    obtain ⟨φ, hφ, h⟩ := on x
    exact ⟨φ, hφ, by rw [LinearMap.comp_apply, h, hx]⟩
  · rw [e', eq_top_iff]
    intro x _
    obtain ⟨φ, hφ, h⟩ := on' x
    exact ⟨φ, hφ, by rw [LinearMap.comp_apply, h, hx]⟩
  · rw [e]
    exact (coef_aug L hl.aug).trans (LinearMap.ker_le_ker_comp _ _)
  · rw [e']
    exact (coef_aug L' hl'.aug).trans (LinearMap.ker_le_ker_comp _ _)
  · intro h hh φ hφ φ' hφ' φ₁ _ φ₁' _ a1 a2 heq
    rw [e, e'] at heq ⊢
    rw [(L.acts 1 o1 h hh φ hφ _).1 a1, (L'.acts 1 o1' h hh φ' hφ' _).1 a2]
    have := inj _ (mc _ hφ) _ (mc' _ hφ') heq
    change π (c (ω (1, h) φ)) = π (c' (ω' (1, h) φ'))
    rw [hc, hc', coef_transl L hh hφ, coef_transl L' hh hφ', ← hc, ← hc', this]
  · intro N hN
    rw [e] at hN
    by_cases hb : N = ⊥
    · exact Or.inl hb
    right
    obtain ⟨y, hyN, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb
    obtain ⟨φ, hφ, hcφ⟩ := on y
    have hc0 : c φ ≠ 0 := fun h => hy0 (by rw [← hx y, ← hcφ, h, map_zero])
    obtain ⟨h, hU, m, k, cc, hcc, hk, hsum⟩ := reach_vac L V1 hl hφ hc0
    have hψ := L.pres 1 o1 h hU φ hφ
    have step : ∀ g ∈ UAt σ G.W (evFin F v), ∀ χ ∈ SB _, π (c χ) ∈ N → π (c (ω (1, g) χ)) ∈ N := fun g hg χ hχ hN' =>
      hN g hg χ hχ _ (L.pres 1 o1 g hg χ hχ) ((L.acts 1 o1 g hg χ hχ _).2 rfl) hN'
    have hyφ : π (c φ) ∈ N := by rw [hcφ, hx]; exact hyN
    have h1 : π (c (ω (1, h) φ)) ∈ N := step h hU φ hφ hyφ
    have h2 : ∀ i, π (c (ω (1, k i) (ω (1, h) φ))) ∈ N := fun i => step _ (hk i).1 _ hψ h1
    have h3 : π (c (∑ i, ω (1, k i) (ω (1, h) φ))) ∈ N := by
      rw [map_sum, map_sum]; exact Submodule.sum_mem _ fun i _ => h2 i
    have h4 : c (∑ i, ω (1, k i) (ω (1, h) φ)) = cc • c (G.M.vac v) := by
      have := (LinearMap.mem_ker).1 (coef_aug L hl.aug hsum)
      rw [map_sub, sub_eq_zero, map_smul] at this
      rw [hc]; exact this
    rw [h4, map_smul] at h3
    have hv0 : π (c (G.M.vac v)) ∈ N := by
      have := N.smul_mem cc⁻¹ h3; rwa [smul_smul, inv_mul_cancel₀ hcc, one_smul] at this
    have hall : ∀ g ∈ UAt σ G.W (evFin F v), π (c (ω (1, g) (G.M.vac v))) ∈ N := fun g hg => step g hg _ hs hv0
    rw [eq_top_iff]
    intro x _
    have hle : S ≤ N.map S.subtype := by
      change transl (c (G.M.vac v)) v ≤ _
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, hg, rfl⟩
      have hmem : c (ω (1, g) (G.M.vac v)) ∈ S := mc _ (L.pres 1 o1 g hg _ hs)
      refine ⟨_, hall g hg, ?_⟩
      rw [hπ' _ hmem]
      change c (ω (1, g) (G.M.vac v)) = _
      rw [hc, coef_transl L hg hs]
    obtain ⟨z, hz, hzx⟩ := hle x.2
    have : z = x := Subtype.ext hzx
    exact this ▸ hz
  · rw [e, e']
    refine ⟨by rw [LinearMap.comp_apply, LinearMap.comp_apply, eΩ], hne⟩

theorem finInert_of (hV : VacInert) (hF : SphFun) (hA : LocRepEx) : FinInert := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨hv, he⟩
  have P : PairOK B G.V G.W G.M om := ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩
  have P' : PairOK B G.V' G.W G.M' om' := ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩
  obtain ⟨ω, ρ, L⟩ := hA F E σ _ _ B _ _ _ _ P v
  obtain ⟨ω', ρ', L'⟩ := hA F E σ _ _ B _ _ _ _ P' v
  obtain ⟨V1, V2⟩ := hV F E σ B a a' G X om om' hT v he
  have V1 := V1 ω ρ L
  have V2 := V2 ω' ρ' L'
  obtain ⟨l, l', hl, hl', hΩ⟩ := hF F E σ B a a' G X om om' hT v he ω ρ ω' ρ' L L' V1.fixW V2.fixW
  exact finAt_sph L L' hv (hT.geo.hM.vac v).1 (hT.geo.hM'.vac v).1 V1 V2 hl hl' hΩ

end PositivityTheory.Sph

end
