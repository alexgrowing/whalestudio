import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionFree
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero

noncomputable section

namespace Formalism.MainNotions.N.Ln34.UnivLinkPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem univLinkPf_PiNS_anti (T : LocLat G Qp LL O) (π' : LetA O n) {j k : ℕ} (h : j ≤ k)
    {x : W.DD T} (hx : x ∈ PiNS W T π' k) : x ∈ PiNS W T π' j := by
  rw [PiNS, Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_map] at hx ⊢
  obtain ⟨⟨y, hy, rfl⟩, hx2⟩ := hx
  refine ⟨⟨π' ^ (k - j) • y, Submodule.smul_mem _ _ hy, ?_⟩, hx2⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, ← pow_add, Nat.add_sub_cancel' h]

theorem univLinkPf_InvS_anti (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)
    {j k : ℕ} (h : j ≤ k) {x : W.DD T} (hx : x ∈ InvS W T π' Eπ h' k c) : x ∈ InvS W T π' Eπ h' j c := by
  rw [InvS, Submodule.mem_inf, Submodule.mem_comap] at hx ⊢
  exact ⟨hx.1, univLinkPf_PiNS_anti W T π' h hx.2⟩

theorem univLinkPf_cocycle {T : LocLat G Qp LL O} {y z : W.DD T} (h : (y, z) ∈ W.wachCocyclesDelta T) :
    W.γD T W.gamK y - y = W.φD T z - z := by
  have h1 := ((Formalism.MainNotions.LiftingTheory.lifta_mem_Z1DΔ W T y z).mp h).1
  try simp only [herrCocycles, Set.mem_setOf_eq, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h1
  simp only [LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply] at h1
  rw [← sub_eq_zero, sub_eq_add_neg]
  exact h1

theorem univLinkPf_cocycleΔ {T : LocLat G Qp LL O} {y z : W.DD T} (h : (y, z) ∈ W.wachCocyclesDelta T) :
    ∀ δ ∈ W.DelF, W.γD T δ y = y ∧ W.γD T δ z = z := ((Formalism.MainNotions.LiftingTheory.lifta_mem_Z1DΔ W T y z).mp h).2

theorem univLinkPf_mem_Z1DΔ {T : LocLat G Qp LL O} (y z : W.DD T) (hy : ∀ δ ∈ W.DelF, W.γD T δ y = y)
    (hz : ∀ δ ∈ W.DelF, W.γD T δ z = z) (h : W.γD T W.gamK y - y = W.φD T z - z) :
    (y, z) ∈ W.wachCocyclesDelta T := by
  refine (Formalism.MainNotions.LiftingTheory.lifta_mem_Z1DΔ W T y z).mpr ⟨?_, fun δ hδ => ⟨hy δ hδ, hz δ hδ⟩⟩
  try simp only [herrCocycles, Set.mem_setOf_eq, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
  simp only [LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply]
  rw [← sub_eq_add_neg, sub_eq_zero]
  exact h

section Map

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)

theorem univLinkPf_map_DelS {x : W.DD T₁} (hx : ∀ δ ∈ W.DelF, W.γD T₁ δ x = x) :
    ∀ δ ∈ W.DelF, W.γD T₂ δ (W.map F x) = W.map F x := by
  intro δ hδ
  rw [← W.map_γ F δ x, hx δ hδ]

theorem univLinkPf_map_PiNS (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (π' : LetA O n) (k : ℕ)
    {x : W.DD T₁} (hx : x ∈ PiNS W T₁ π' k) : W.map F x ∈ PiNS W T₂ π' k := by
  have hDel : ∀ {T : LocLat G Qp LL O} {x : W.DD T}, x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro T x
    simp [DelS, Submodule.mem_iInf, sub_eq_zero]
  rw [PiNS, Submodule.mem_inf, Submodule.restrictScalars_mem, Formalism.MainNotions.DeltaInvariantLattices.aN, Submodule.mem_map] at hx ⊢
  obtain ⟨⟨y, hy, rfl⟩, hx2⟩ := hx
  refine ⟨⟨W.map F y, W.map_N F h1 h2 y hy, ?_⟩, hDel.mpr (univLinkPf_map_DelS W F (hDel.mp hx2))⟩
  simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply]
  exact ((Formalism.MainNotions.DeltaInvariantLattices.mapA W F).map_smul _ _).symm

theorem univLinkPf_map_φspan (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (c : ZMod n) {x : W.DD T₁}
    (hx : x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₁ (W.Nl T₁ c)) : W.map F x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ c) := by
  have hNl : ∀ y ∈ W.Nl T₁ c, W.map F y ∈ W.Nl T₂ c := by
    intro y hy
    unfold Formalism.BasicNotions.LocWach.Nl at hy ⊢
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    refine Submodule.mem_map.mpr ⟨W.map F z, W.map_N F h1 h2 z hz, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    exact ((Formalism.MainNotions.DeltaInvariantLattices.mapA W F).map_smul _ _).symm
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan at hx ⊢
  have hm : (Formalism.MainNotions.DeltaInvariantLattices.mapA W F) x ∈ Submodule.map (Formalism.MainNotions.DeltaInvariantLattices.mapA W F)
      (Submodule.span (LetA O n) (W.φD T₁ '' (W.Nl T₁ c : Set (W.DD T₁)))) := Submodule.mem_map_of_mem hx
  rw [Submodule.map_span] at hm
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨W.map F y, hNl y hy, (W.map_φ F y).symm⟩

theorem univLinkPf_map_LamPS (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (Eπ : LetA O n) (h' : ℕ)
    (c : ZMod n) {x : W.DD T₁} (hx : x ∈ LamPS W T₁ Eπ h' c) : W.map F x ∈ LamPS W T₂ Eπ h' c := by
  have hDel : ∀ {T : LocLat G Qp LL O} {x : W.DD T}, x ∈ DelS W T ↔ ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    intro T x
    simp [DelS, Submodule.mem_iInf, sub_eq_zero]
  have hsm : ∀ (a : LetA O n) (y : W.DD T₁), W.map F (a • y) = a • W.map F y :=
    fun a y => (Formalism.MainNotions.DeltaInvariantLattices.mapA W F).map_smul a y
  rw [LamPS, Submodule.mem_inf, Submodule.mem_inf] at hx ⊢
  obtain ⟨⟨hA, hB⟩, hC⟩ := hx
  refine ⟨⟨?_, hDel.mpr (univLinkPf_map_DelS W F (hDel.mp hB))⟩, ?_⟩
  · rw [Submodule.restrictScalars_mem, Submodule.mem_comap] at hA ⊢
    have hφ := univLinkPf_map_φspan W F h1 h2 (c - 1) hA
    simp only [Formalism.MainNotions.DeltaInvariantLattices.smulA, LinearMap.smul_apply, LinearMap.id_apply] at hφ ⊢
    rw [hsm] at hφ
    exact hφ
  · rw [letS, LinearMap.mem_ker] at hC ⊢
    simp only [LinearMap.restrictScalars_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hC ⊢
    rw [← hsm, ← map_sub, hC, map_zero]

theorem univLinkPf_map_InvS (h1 : IsCrys PD T₁.ρ) (h2 : IsCrys PD T₂.ρ) (π' Eπ : LetA O n) (h' k : ℕ)
    (c : ZMod n) {x : W.DD T₁} (hx : x ∈ InvS W T₁ π' Eπ h' k c) : W.map F x ∈ InvS W T₂ π' Eπ h' k c := by
  rw [InvS, Submodule.mem_inf, Submodule.mem_comap] at hx ⊢
  refine ⟨univLinkPf_map_LamPS W F h1 h2 Eπ h' c hx.1, ?_⟩
  have hP := univLinkPf_map_PiNS W F h1 h2 π' k hx.2
  simp only [LinearMap.sub_apply, LinearMap.id_apply] at hP ⊢
  rw [map_sub, W.map_γ] at hP
  exact hP

theorem univLinkPf_map_Z1DΔ {y z : W.DD T₁} (h : (y, z) ∈ W.wachCocyclesDelta T₁) :
    (W.map F y, W.map F z) ∈ W.wachCocyclesDelta T₂ := by
  have hc := univLinkPf_cocycle W h
  have hd := univLinkPf_cocycleΔ W h
  apply univLinkPf_mem_Z1DΔ W
  · exact univLinkPf_map_DelS W F (fun δ hδ => (hd δ hδ).1)
  · exact univLinkPf_map_DelS W F (fun δ hδ => (hd δ hδ).2)
  · rw [← W.map_γ, ← W.map_φ, ← map_sub, ← map_sub, hc]

end Map

section Frame

variable (T : LocLat G Qp LL O)

theorem univLinkPf_toLA_eq (π' : LetA O n) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    toLA W T π' c S = (toLA W T π' c ⊤).comp (TensorProduct.map LinearMap.id (Submodule.inclusion le_top)) := by
  unfold toLA
  rw [← TensorProduct.map_comp, LinearMap.comp_id, Submodule.subtype_comp_inclusion]

theorem univLinkPf_LamLA_le (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    LamLA W T π' Eπ h' c S ≤ LamLA W T π' Eπ h' c ⊤ := by
  unfold LamLA
  refine Submodule.comap_mono ?_
  rw [univLinkPf_toLA_eq W T π' c S]
  exact LinearMap.range_comp_le_range _ _

theorem univLinkPf_InvL_le (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (π' Eπ : LetA O n) (h' : ℕ)
    (c : ZMod n) (S : Submodule O (LcQ W T π' c)) :
    InvL W T Pt π' Eπ h' c S ≤ InvL W T Pt π' Eπ h' c ⊤ := by
  unfold InvL
  exact inf_le_inf_right _ (univLinkPf_LamLA_le W T π' Eπ h' c S)

theorem univLinkPf_basis [StrongRankCondition O] (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n) (S : Submodule O (LcQ W T π' c))
    [Module.Finite O (IIrest W T Pt π' Eπ h' c S)] [Module.Free O (IIrest W T Pt π' Eπ h' c S)] :
    ∃ xb : Fin (finrank O (IIrest W T Pt π' Eπ h' c S)) → ↥(InvL W T Pt π' Eπ h' c S),
      ∀ x : ↥(InvL W T Pt π' Eπ h' c S), ∃ o : Fin (finrank O (IIrest W T Pt π' Eπ h' c S)) → O,
        (x : LA W T π' c) - ∑ i, o i • (xb i : LA W T π' c) ∈ piNL W T Pt π' Eπ h' c 1 := by
  classical
  let b := Module.finBasis O (IIrest W T Pt π' Eπ h' c S)
  choose xb hxb using fun i => Submodule.Quotient.mk_surjective _ (b i)
  refine ⟨xb, fun x => ⟨fun i => b.repr (Submodule.Quotient.mk x) i, ?_⟩⟩
  have h : (Submodule.Quotient.mk x : IIrest W T Pt π' Eπ h' c S) =
      Submodule.Quotient.mk (∑ i, b.repr (Submodule.Quotient.mk x) i • xb i) := by
    rw [show (Submodule.Quotient.mk (∑ i, b.repr (Submodule.Quotient.mk x) i • xb i) :
        IIrest W T Pt π' Eπ h' c S) =
        Submodule.mkQ _ (∑ i, b.repr (Submodule.Quotient.mk x) i • xb i) from rfl]
    simp only [map_sum, map_smul, Submodule.mkQ_apply, hxb]
    exact (b.sum_repr _).symm
  rw [Submodule.Quotient.eq] at h
  simpa using h

theorem univLinkPf_JP {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M : ℕ}
    {c : ZMod n} {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hMF : ModelF W T Pt π' Eπ h' M c α β) (hM : 1 ≤ M) (y : ↥(LamPS W T Eπ h' c))
    (hJ : Submodule.Quotient.mk y = (0 : QLamP W T π' Eπ h' M c)) : (y : W.DD T) ∈ PiNS W T π' M := by
  refine (hMF.2.2.1 M hM le_rfl).1 0 (Submodule.zero_mem _) y.1 y.2 ?_ (Submodule.zero_mem _)
  show α T 0 = _
  rw [map_zero]
  exact hJ.symm

theorem univLinkPf_transport {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M : ℕ}
    {c : ZMod n} {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hMF : ModelF W T Pt π' Eπ h' M c α β) (hM : 1 ≤ M) {k r : ℕ}
    (X : ↥(LamLA W T π' Eπ h' c ⊤)) (Y : ↥(LamPS W T Eπ h' c))
    (hX : α T X = Submodule.Quotient.mk Y)
    (Xj : Fin k → ↥(LamLA W T π' Eπ h' c ⊤)) (Yj : Fin k → ↥(LamPS W T Eπ h' c))
    (hXj : ∀ j, α T (Xj j) = Submodule.Quotient.mk (Yj j))
    (Xb : Fin r → ↥(LamLA W T π' Eπ h' c ⊤)) (Yb : Fin r → ↥(LamPS W T Eπ h' c))
    (hXb : ∀ i, α T (Xb i) = Submodule.Quotient.mk (Yb i)) (o : Fin r → O)
    (hrel : (X : LA W T π' c) - ∑ j, (Xj j : LA W T π' c) - ∑ i, o i • (Xb i : LA W T π' c) ∈
      piNL W T Pt π' Eπ h' c 1) :
    (Y : W.DD T) - ∑ j, (Yj j : W.DD T) - ∑ i, o i • (Yb i : W.DD T) ∈ PiNS W T π' 1 := by
  have h3 := (hMF.2.2.1 1 le_rfl hM).1
  have hαx : α T (X - ∑ j, Xj j - ∑ i, o i • Xb i) =
      Submodule.Quotient.mk (Y - ∑ j, Yj j - ∑ i, o i • Yb i) := by
    rw [show (Submodule.Quotient.mk (Y - ∑ j, Yj j - ∑ i, o i • Yb i) : QLamP W T π' Eπ h' M c) =
      Submodule.mkQ _ (Y - ∑ j, Yj j - ∑ i, o i • Yb i) from rfl]
    simp only [map_sub, map_sum, map_smul, Submodule.mkQ_apply, hX, hXj, hXb]
  have hmem := h3 ((X - ∑ j, Xj j - ∑ i, o i • Xb i : ↥(LamLA W T π' Eπ h' c ⊤)) : LA W T π' c)
    (X - ∑ j, Xj j - ∑ i, o i • Xb i).2
    ((Y - ∑ j, Yj j - ∑ i, o i • Yb i : ↥(LamPS W T Eπ h' c)) : W.DD T)
    (Y - ∑ j, Yj j - ∑ i, o i • Yb i).2 hαx (by simpa using hrel)
  simpa using hmem

end Frame

end Local

end Formalism.MainNotions.N.Ln34.UnivLinkPf

end
