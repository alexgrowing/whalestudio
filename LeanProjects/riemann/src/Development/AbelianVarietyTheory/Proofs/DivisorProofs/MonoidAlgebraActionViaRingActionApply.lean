import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
import Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne

open Module GlobalTheory.HTRho

noncomputable section

namespace GlobalTheory.HTRho.FilDim

variable {k H O C : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O]

theorem mSub_gen (σ : O →+* Module.End k H) (χ : C →+* k) {X : Submodule k H} (c : C) {x : H}
    (hx : x ∈ X) : σ (algebraMap C O c) x - χ c • x ∈ mSub σ χ X :=
  Submodule.subset_span ⟨c, x, hx, rfl⟩

theorem mSub_le_of_stable (σ : O →+* Module.End k H) (χ : C →+* k) (X : Submodule k H)
    (hX : ∀ a, ∀ x ∈ X, σ a x ∈ X) : mSub σ χ X ≤ X := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨c, x, hx, rfl⟩
  exact X.sub_mem (hX _ x hx) (X.smul_mem _ hx)

theorem mSub_mono (σ : O →+* Module.End k H) (χ : C →+* k) {X Y : Submodule k H} (h : X ≤ Y) :
    mSub σ χ X ≤ mSub σ χ Y := by
  refine Submodule.span_mono ?_
  rintro _ ⟨c, x, hx, rfl⟩
  exact ⟨c, x, h hx, rfl⟩

theorem jSub_mono {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) {X Y : Submodule k H}
    (h : X ≤ Y) : jSub σ χ X ≤ jSub σ χ Y := by
  refine Submodule.span_mono ?_
  rintro _ ⟨r, lam, c, x, hx, hc, rfl⟩
  exact ⟨r, lam, c, x, h hx, hc, rfl⟩

theorem jSub_le_mSub {ι : Type*} (σ : O →+* Module.End k H) (χ : ι → C →+* k) (X : Submodule k H)
    (i : ι) : jSub σ χ X ≤ mSub σ (χ i) X := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨r, lam, c, x, hx, hc, rfl⟩
  have e : ∑ l, lam l • σ (algebraMap C O (c l)) x
      = ∑ l, lam l • (σ (algebraMap C O (c l)) x - χ i (c l) • x) + (∑ l, lam l * χ i (c l)) • x := by
    simp only [smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, smul_smul]
    abel
  rw [e, hc i, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (mSub_gen σ (χ i) (c l) hx)

theorem jSub_gen {ι β : Type*} [Fintype β] (σ : O →+* Module.End k H) (χ : ι → C →+* k)
    {X : Submodule k H} (lam : β → k) (c : β → C) {x : H} (hx : x ∈ X)
    (h : ∀ i, ∑ l, lam l * χ i (c l) = 0) :
    ∑ l, lam l • σ (algebraMap C O (c l)) x ∈ jSub σ χ X := by
  let e := Fintype.equivFin β
  refine Submodule.subset_span ⟨Fintype.card β, lam ∘ e.symm, c ∘ e.symm, x, hx, fun i => ?_, ?_⟩
  · rw [← h i]; exact Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
  · exact (Fintype.sum_equiv e.symm _ _ (fun _ => rfl)).symm

theorem mSub_rAct (σ : O →+* Module.End k H) (χ : C →+* k) (G : Submodule k H)
    (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) :
    (mSub (rAct σ G hG) χ ⊤).map G.subtype = mSub σ χ G := by
  rw [mSub, Submodule.map_span, mSub]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨c, x, _, rfl⟩, rfl⟩
    exact ⟨c, x, x.2, by simp⟩
  · rintro ⟨c, x, hx, rfl⟩
    exact ⟨_, ⟨c, ⟨x, hx⟩, trivial, rfl⟩, by simp⟩

theorem mSub_qAct {V : Type*} [AddCommGroup V] [Module k V] (τ : O →+* Module.End k V) (χ : C →+* k)
    (X : Submodule k V) (h : ∀ a, ∀ x ∈ X, τ a x ∈ X) :
    mSub (qAct τ X h) χ ⊤ = (mSub τ χ ⊤).map X.mkQ := by
  simp only [mSub]
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨c, q, _, rfl⟩
    obtain ⟨x, rfl⟩ := X.mkQ_surjective q
    exact ⟨_, ⟨c, x, trivial, rfl⟩, by simp; rfl⟩
  · rintro ⟨w, ⟨c, x, _, rfl⟩, rfl⟩
    exact ⟨c, X.mkQ x, trivial, by simp; rfl⟩

theorem exists_delta {Idx : Type*} [Fintype Idx] [DecidableEq Idx] (χ : Idx → C →+* k)
    (hχ : Function.Injective χ) (i : Idx) :
    ∃ S : Finset C, ∃ lam : C → k, ∀ j, ∑ d ∈ S, lam d * χ j d = if j = i then 1 else 0 := by
  let v : C → (Idx → k) := fun d j => χ j d
  have hmem : (Pi.single i 1 : Idx → k) ∈ Submodule.span k (Set.range v) := by
    by_contra hx
    obtain ⟨f, hf, hf'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hx inferInstance
    have hli : LinearIndependent k (fun j => ((χ j : C →* k) : C → k)) := by
      have := linearIndependent_monoidHom C k
      refine this.comp (fun j => (χ j : C →* k)) ?_
      intro a b hab
      apply hχ
      ext c
      exact DFunLike.congr_fun hab c
    have hzero : ∑ j, f (Pi.single j 1) • ((χ j : C →* k) : C → k) = 0 := by
      funext d
      have h1 : f (v d) = 0 := by
        have : f (v d) ∈ (Submodule.span k (Set.range v)).map f :=
          Submodule.mem_map_of_mem (Submodule.subset_span ⟨d, rfl⟩)
        rw [hf'] at this
        exact this
      rw [LinearMap.pi_apply_eq_sum_univ f (v d)] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [v, smul_eq_mul, MonoidHom.coe_coe]
      rw [mul_comm]
      congr 2
      funext j'
      simp [Pi.single_apply, eq_comm]
    have ha := Fintype.linearIndependent_iff.1 hli _ hzero
    apply hf
    rw [LinearMap.pi_apply_eq_sum_univ f (Pi.single i 1)]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hs : (fun j' => if j = j' then (1 : k) else 0) = Pi.single j 1 := by
      funext j'; simp [Pi.single_apply, eq_comm]
    rw [hs, ha j, smul_zero]
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨c.support, c, fun j => ?_⟩
  have := congrFun hc j
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, v] at this
  rw [this, Pi.single_apply]

theorem mSub_map_le (σ : O →+* Module.End k H) (χ : C →+* k) (T : Module.End k H)
    (hT : ∀ c z, T (σ (algebraMap C O c) z) = σ (algebraMap C O c) (T z)) :
    (mSub σ χ ⊤).map T ≤ mSub σ χ (LinearMap.range T) := by
  rw [mSub, Submodule.map_span]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨c, z, _, rfl⟩, rfl⟩
  refine Submodule.subset_span ⟨c, T z, ⟨z, rfl⟩, ?_⟩
  simp [hT]

theorem inf_le_sup {Idx : Type*} [Fintype Idx] (σ : O →+* Module.End k H) (χ : Idx → C →+* k)
    (hχ : Function.Injective χ) (G : Submodule k H) (hG : ∀ a, ∀ x ∈ G, σ a x ∈ G) (ω : C) (r₀ r₁ : k)
    (hr : r₀ ≠ r₁)
    (hw : (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0)
    (hχω : ∀ i, χ i ω = r₀) (hR : LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) ≤ G) (i : Idx) :
    G ⊓ mSub σ (χ i) ⊤ ≤
      jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) ⊔ mSub σ (χ i) G := by
  classical
  have hA : LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) ≤ mSub σ (χ i) G := by
    rintro y ⟨z, rfl⟩
    have h0 : ((σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1)) z = 0 := by
      rw [hw]; rfl
    have e1 : σ (algebraMap C O ω) ((σ (algebraMap C O ω) - r₀ • 1) z) - r₀ • (σ (algebraMap C O ω) - r₀ • 1) z
        = (r₁ - r₀) • (σ (algebraMap C O ω) - r₀ • 1) z := by
      have : σ (algebraMap C O ω) ((σ (algebraMap C O ω) - r₀ • 1) z) - r₀ • (σ (algebraMap C O ω) - r₀ • 1) z
          = ((σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1)) z
            + (r₁ - r₀) • (σ (algebraMap C O ω) - r₀ • 1) z := by
        simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
          map_sub, map_smul]
        module
      rw [this, h0, zero_add]
    have hg := mSub_gen σ (χ i) ω (hR ⟨z, rfl⟩)
    rw [hχω i, e1] at hg
    have hne : r₁ - r₀ ≠ 0 := sub_ne_zero.2 (Ne.symm hr)
    have := Submodule.smul_mem _ (r₁ - r₀)⁻¹ hg
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  have hcomm : ∀ c z, (σ (algebraMap C O ω) - r₁ • 1) (σ (algebraMap C O c) z)
      = σ (algebraMap C O c) ((σ (algebraMap C O ω) - r₁ • 1) z) := by
    intro c z
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul]
    congr 1
    have : algebraMap C O ω * algebraMap C O c = algebraMap C O c * algebraMap C O ω := by
      rw [← map_mul, mul_comm, map_mul]
    rw [← Module.End.mul_apply, ← map_mul σ, this, map_mul σ, Module.End.mul_apply]
  rintro x ⟨hxG, hxM⟩
  have hx : x = (r₀ - r₁)⁻¹ • (σ (algebraMap C O ω) - r₁ • 1) x
      - (r₀ - r₁)⁻¹ • (σ (algebraMap C O ω) - r₀ • 1) x := by
    have hne : r₀ - r₁ ≠ 0 := sub_ne_zero.2 hr
    have : (σ (algebraMap C O ω) - r₁ • 1) x - (σ (algebraMap C O ω) - r₀ • 1) x = (r₀ - r₁) • x := by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      module
    rw [← smul_sub, this, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hq : (σ (algebraMap C O ω) - r₀ • 1) x ∈ mSub σ (χ i) G := hA ⟨x, rfl⟩
  set p := (σ (algebraMap C O ω) - r₁ • 1) x with hp_def
  have hpG : p ∈ G := by
    rw [hp_def]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact G.sub_mem (hG _ x hxG) (G.smul_mem _ hxG)
  have hpR : p ∈ mSub σ (χ i) (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) :=
    mSub_map_le σ (χ i) _ hcomm (Submodule.mem_map_of_mem hxM)
  obtain ⟨S, lam, hδ⟩ := exists_delta χ hχ i
  let E : Module.End k H := ∑ d ∈ S, lam d • σ (algebraMap C O d)
  have hEapp : ∀ v, E v = ∑ d ∈ S, lam d • σ (algebraMap C O d) v := by
    intro v; simp [E, LinearMap.sum_apply]
  have hE : ∀ v ∈ mSub σ (χ i) (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)),
      E v ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, hy, rfl⟩ := hz
      have key := jSub_gen σ χ (β := S ⊕ S)
        (Sum.elim (fun d => lam d) (fun d => -(lam d * χ i c)))
        (Sum.elim (fun d => (d : C) * c) (fun d => (d : C))) hy (by
          intro j
          rw [Fintype.sum_sum_type]
          simp only [Sum.elim_inl, Sum.elim_inr, map_mul]
          rw [Finset.sum_coe_sort S (fun d => lam d * (χ j d * χ j c)),
            Finset.sum_coe_sort S (fun d => -(lam d * χ i c) * χ j d)]
          have h1 : ∑ d ∈ S, lam d * (χ j d * χ j c) = (∑ d ∈ S, lam d * χ j d) * χ j c := by
            rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun d _ => by ring
          have h2 : ∑ d ∈ S, -(lam d * χ i c) * χ j d = -(χ i c) * ∑ d ∈ S, lam d * χ j d := by
            rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
          rw [h1, h2, hδ j]
          split_ifs with h
          · subst h; ring
          · ring)
      convert key using 1
      rw [hEapp, Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, map_mul, Module.End.mul_apply, neg_smul, Finset.sum_neg_distrib]
      rw [Finset.sum_coe_sort S (fun d => lam d • σ (algebraMap C O d) (σ (algebraMap C O c) y)),
        Finset.sum_coe_sort S (fun d => (lam d * χ i c) • σ (algebraMap C O d) y)]
      simp only [map_sub, map_smul, smul_sub, Finset.sum_sub_distrib, smul_smul]
      rw [sub_eq_add_neg]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  have hpE : p - E p ∈ mSub σ (χ i) G := by
    have : p - E p = -∑ d ∈ S, lam d • (σ (algebraMap C O d) p - χ i d • p) := by
      rw [hEapp]
      simp only [smul_sub, Finset.sum_sub_distrib, smul_smul]
      rw [← Finset.sum_smul, hδ i, if_pos rfl, one_smul]
      abel
    rw [this]
    exact neg_mem (Submodule.sum_mem _ fun d _ => Submodule.smul_mem _ _ (mSub_gen σ (χ i) d hpG))
  have hp : p ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)) ⊔ mSub σ (χ i) G := by
    have : p = E p + (p - E p) := by abel
    rw [this]
    exact Submodule.add_mem_sup (hE p hpR) hpE
  rw [hx]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hp)
    (Submodule.smul_mem _ _ (Submodule.mem_sup_right hq))

end GlobalTheory.HTRho.FilDim

open Module GlobalTheory.HTRho GlobalTheory.UPel.Sm GlobalTheory.UPel.Sm.Model

theorem GlobalTheory.HTRho.FilDim.finrank_fildim : ∀ {k O C Idx H : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O] [CommRing C] [Algebra C O] [Fintype Idx] [FiniteDimensional k H] (σ : O →+* Module.End k H) (χ : Idx → C →+* k), Function.Injective χ → ∀ (Fil : Submodule k H), (∀ a, ∀ x ∈ Fil, σ a x ∈ Fil) → ∀ (ω : C) (r₀ r₁ : k), r₀ ≠ r₁ → (σ (algebraMap C O ω) - r₀ • 1) * (σ (algebraMap C O ω) - r₁ • 1) = 0 → (∀ i, χ i ω = r₀) → ∀ (hG : ∀ a, ∀ x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1), σ a x ∈ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1)) (hZ : ∀ a, ∀ x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)), σ a x ∈ jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1))), jSub σ χ ⊤ ≤ Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1) → ∀ (i : Idx), let G := Fil ⊔ LinearMap.range (σ (algebraMap C O ω) - r₀ • 1); let Z := jSub σ χ (LinearMap.range (σ (algebraMap C O ω) - r₁ • 1)); let σW := qAct (rAct σ G hG) (Z.comap G.subtype) (fun a x hx => hZ a x hx); finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) + finrank k (H ⧸ (G ⊔ mSub σ (χ i) ⊤)) = finrank k (H ⧸ mSub σ (χ i) ⊤) := by
  intro k O C Idx H _ _ _ _ _ _ _ _ σ χ hχ Fil hFil ω r₀ r₁ hr hw hχω hG hZ hJ i G Z σW
  classical
  have hZG : Z ≤ G := (GlobalTheory.HTRho.FilDim.jSub_mono σ χ le_top).trans hJ
  have hZM : Z ≤ mSub σ (χ i) ⊤ :=
    (GlobalTheory.HTRho.FilDim.jSub_le_mSub σ χ _ i).trans (GlobalTheory.HTRho.FilDim.mSub_mono σ (χ i) le_top)
  have hmG : mSub σ (χ i) G ≤ G ⊓ mSub σ (χ i) ⊤ :=
    le_inf (GlobalTheory.HTRho.FilDim.mSub_le_of_stable σ _ G hG) (GlobalTheory.HTRho.FilDim.mSub_mono _ _ le_top)
  have heq : Z ⊔ mSub σ (χ i) G = G ⊓ mSub σ (χ i) ⊤ :=
    le_antisymm (sup_le (le_inf hZG hZM) hmG)
      (GlobalTheory.HTRho.FilDim.inf_le_sup σ χ hχ G hG ω r₀ r₁ hr hw hχω le_sup_right i)
  let N : Submodule k G := mSub (rAct σ G hG) (χ i) ⊤ ⊔ Z.comap G.subtype
  have hσW : mSub σW (χ i) ⊤ = N.map (Z.comap G.subtype).mkQ := by
    refine (GlobalTheory.HTRho.FilDim.mSub_qAct (rAct σ G hG) (χ i) (Z.comap G.subtype) _).trans ?_
    simp only [N]
    rw [Submodule.map_sup, Submodule.mkQ_map_self, sup_bot_eq]
  have e1 : finrank k ((G ⧸ Z.comap G.subtype) ⧸ mSub σW (χ i) ⊤) = finrank k (G ⧸ N) := by
    rw [hσW]
    exact (Submodule.quotientQuotientEquivQuotient (Z.comap G.subtype) N le_sup_right).finrank_eq
  have hNmap : N.map G.subtype = G ⊓ mSub σ (χ i) ⊤ := by
    simp only [N]
    rw [Submodule.map_sup, GlobalTheory.HTRho.FilDim.mSub_rAct, Submodule.map_comap_subtype,
      inf_eq_right.2 hZG, sup_comm, heq]
  have e2 : finrank k N = finrank k ↥(G ⊓ mSub σ (χ i) ⊤) := by
    have := (Submodule.equivMapOfInjective G.subtype G.injective_subtype N).finrank_eq
    rw [hNmap] at this
    exact this
  have a1 := Submodule.finrank_quotient_add_finrank N
  have a2 := Submodule.finrank_quotient_add_finrank (G ⊔ mSub σ (χ i) ⊤)
  have a3 := Submodule.finrank_quotient_add_finrank (mSub σ (χ i) ⊤)
  have a4 := Submodule.finrank_sup_add_finrank_inf_eq G (mSub σ (χ i) ⊤)
  rw [e1]
  omega
