import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.UnivLinkPfA

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

theorem univLinkPf_map_osmul {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (a : O)
    (x : W.DD T₁) : W.map F (a • x) = a • W.map F x :=
  LinearMap.map_smul_of_tower ((W.map F).restrictScalars (LetA O n)) a x

theorem univLinkPf_liftsBy_mono {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {π' Eπ : LetA O n}
    {h' y : ℕ} {c : ZMod n} {z : W.DD T₂} (t : ℕ) (h : LiftsBy W F π' Eπ h' y c z) :
    LiftsBy W F π' Eπ h' (y + t) c z := by
  obtain ⟨hz, w₁, hw₁, hr⟩ := h
  refine ⟨hz, ((PD.p : ℕ) : O) ^ t • w₁, Submodule.smul_mem _ _ hw₁, ?_⟩
  have h2 := Submodule.smul_mem (PiNS W T₂ π' 1) (((PD.p : ℕ) : O) ^ t) hr
  rwa [smul_sub, smul_smul, ← pow_add, add_comm t y, ← univLinkPf_map_osmul] at h2

theorem universal_lift_mono_exponent {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M S : ℕ}
    {up : (K →ₐ[Qp] LL) → Bool} {b : (K →ₐ[Qp] LL) → ℕ} {c : ZMod n} {y : ℕ}
    {α : FrA W π' Eπ h' M c} (h : ThirdPropositionSlot W F Pt π' Eπ h' M S up b c y α) (t : ℕ) :
    ThirdPropositionSlot W F Pt π' Eπ h' M S up b c (y + t) α :=
  fun f hf x hx hFil h1 z hz hα => univLinkPf_liftsBy_mono W F t (h f hf x hx hFil h1 z hz hα)

theorem univLinkPf_cong {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M σ κ y₁ S : ℕ} {c : ZMod n}
    {up : (K →ₐ[Qp] LL) → Bool} {b : (K →ₐ[Qp] LL) → ℕ}
    {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hβα : ∀ y hy x hx, β T₂ ⟨y, hy⟩ = mkLA W T₂ π' Eπ h' M c x hx →
      α T₂ ⟨x, hx⟩ = mkP W T₂ π' Eπ h' M c (((PD.p : ℕ) : O) ^ (2 * σ) • y)
        ((LamPS W T₂ Eπ h' c).smul_mem _ hy))
    (hMF : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M)
    (u : O) (hu : u * piOm1 W c S h' up b = ((PD.p : ℕ) : O) ^ κ)
    (hU3 : ThirdPropositionSlot W F Pt π' Eπ h' M S up b c y₁ α)
    (Lr : Submodule O (LcQ W T₂ π' c)) {k : ℕ} (ell : Fin k → W.DD T₂)
    (hell : ∀ j, ell j ∈ NcS W T₂ (c - 1))
    (hFil : ∀ j τ, Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c → up τ = true → ell j ∈ FilL W T₂ Pt c τ (b τ))
    {r : ℕ} (xb : Fin r → ↥(InvL W T₂ Pt π' Eπ h' c Lr))
    (hxb : ∀ x : ↥(InvL W T₂ Pt π' Eπ h' c Lr), ∃ o : Fin r → O,
      (x : LA W T₂ π' c) - ∑ i, o i • (xb i : LA W T₂ π' c) ∈ piNL W T₂ Pt π' Eπ h' c 1)
    (hxbL : ∀ i, (xb i : LA W T₂ π' c) ∈ LamLA W T₂ π' Eπ h' c ⊤)
    (Yb : Fin r → ↥(LamPS W T₂ Eπ h' c))
    (hYb : ∀ i, α T₂ ⟨xb i, hxbL i⟩ = Submodule.Quotient.mk (Yb i))
    (w : W.DD T₂) (hw : w ∈ InvS W T₂ π' Eπ h' 1 c)
    (hU1w : ∃ (f : Fin k → W.EE) (x : LA W T₂ π' c)
      (hx : x ∈ LamLA W T₂ π' Eπ h' c ⊤) (xr : LA W T₂ π' c),
      (∀ j, IsCoord W Pt π' Eπ h' S up b c (f j)) ∧
      (∀ j, f j ⊗ₜ mkL W T₂ π' c (ell j) (hell j) ∈ InvL W T₂ Pt π' Eπ h' c ⊤) ∧
      xr ∈ InvL W T₂ Pt π' Eπ h' c Lr ∧
      β T₂ ⟨piOm1 W c S h' up b • w, (LamPS W T₂ Eπ h' c).smul_mem _ (Submodule.mem_inf.mp hw).1⟩ =
        mkLA W T₂ π' Eπ h' M c x hx ∧
      x - ∑ j, f j ⊗ₜ mkL W T₂ π' c (ell j) (hell j) - xr ∈ piNL W T₂ Pt π' Eπ h' c 1) :
    ∃ w₁ ∈ InvS W T₁ π' Eπ h' 1 c, ∃ o : Fin r → O,
      ((PD.p : ℕ) : O) ^ (2 * σ + κ + y₁) • w - W.map F w₁ - ∑ i, o i • (Yb i : W.DD T₂) ∈
        PiNS W T₂ π' 1 := by
  obtain ⟨f, x, hx, xr, hcoord, hfl, hxr, hβ, hrel⟩ := hU1w
  have hαx := hβα _ _ x hx hβ
  obtain ⟨o, ho⟩ := hxb ⟨xr, hxr⟩
  let Xj : Fin k → ↥(LamLA W T₂ π' Eπ h' c ⊤) := fun j =>
    ⟨f j ⊗ₜ mkL W T₂ π' c (ell j) (hell j), (Submodule.mem_inf.1 (hfl j)).1⟩
  choose Yj hYj using fun j => Submodule.Quotient.mk_surjective _ (α T₂ (Xj j))
  have hrel' : x - ∑ j, (Xj j : LA W T₂ π' c) -
      ∑ i, o i • ((⟨xb i, hxbL i⟩ : ↥(LamLA W T₂ π' Eπ h' c ⊤)) : LA W T₂ π' c) ∈
      piNL W T₂ Pt π' Eπ h' c 1 := by
    have h := Submodule.add_mem _ hrel ho
    rw [sub_add_sub_cancel] at h
    exact h
  have htr := univLinkPf_transport W T₂ hMF hM ⟨x, hx⟩ _ hαx Xj Yj (fun j => (hYj j).symm)
    (fun i => ⟨xb i, hxbL i⟩) Yb hYb o hrel'
  have hL : ∀ j, LiftsBy W F π' Eπ h' y₁ c (Yj j : W.DD T₂) := fun j =>
    hU3 (f j) (hcoord j) (ell j) (hell j) (hFil j) (Xj j).2 (Yj j) (Yj j).2 (hYj j).symm
  choose w₁ hw₁ hw₁r using fun j => (hL j).2
  refine ⟨∑ j, u • w₁ j, Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ u (hw₁ j),
    fun i => ((PD.p : ℕ) : O) ^ y₁ * u * o i, ?_⟩
  have htr' := (Submodule.Quotient.mk_eq_zero (PiNS W T₂ π' 1)).2 htr
  rw [← Submodule.mkQ_apply] at htr'
  simp only [map_sub, map_sum, map_smul] at htr'
  rw [sub_sub, sub_eq_zero] at htr'
  have hq2 : ∀ j, (PiNS W T₂ π' 1).mkQ (W.map F (w₁ j)) =
      ((PD.p : ℕ) : O) ^ y₁ • (PiNS W T₂ π' 1).mkQ (Yj j : W.DD T₂) := by
    intro j
    have h := (Submodule.Quotient.mk_eq_zero (PiNS W T₂ π' 1)).2 (hw₁r j)
    rw [← Submodule.mkQ_apply, map_sub, map_smul, sub_eq_zero] at h
    exact h.symm
  have hc : ((PD.p : ℕ) : O) ^ (2 * σ + κ + y₁) =
      (((PD.p : ℕ) : O) ^ y₁ * u) * (((PD.p : ℕ) : O) ^ (2 * σ) * piOm1 W c S h' up b) := by
    rw [pow_add, pow_add, ← hu]; ring
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
  simp only [map_sub, map_sum, map_smul, univLinkPf_map_osmul, hq2]
  rw [hc, mul_smul (((PD.p : ℕ) : O) ^ y₁ * u),
    mul_smul (((PD.p : ℕ) : O) ^ (2 * σ)) (piOm1 W c S h' up b), htr', smul_add,
    Finset.smul_sum, Finset.smul_sum]
  simp only [smul_smul]
  rw [mul_comm u (((PD.p : ℕ) : O) ^ y₁)]
  abel

theorem univLinkPf_class {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ) (hK : W.ClKNat)
    {π' Eπ : LetA O n} {h' M σ N : ℕ} {c : ZMod n}
    (hR₁ : InvLift W T₁ π' Eπ h' M σ c) (hR₂ : InvLift W T₂ π' Eπ h' M σ c)
    (hC₁ : ClassMap W T₁ π' Eπ h' M c) (hC₂ : ClassMap W T₂ π' Eπ h' M c)
    {r : ℕ} (Yb : Fin r → W.DD T₂) (Ybb : Fin r → W.DD T₂)
    (hYbb : ∀ i, Ybb i ∈ InvS W T₂ π' Eπ h' M c)
    (hYbbR : ∀ i, ((PD.p : ℕ) : O) ^ σ • Yb i - Ybb i ∈ PiNS W T₂ π' 1)
    (Pb : Fin r → ↥(W.wachCocyclesDelta T₂)) (hPb1 : ∀ i, (Pb i : W.DD T₂ × W.DD T₂).1 = Ybb i)
    (hPb2 : ∀ i, (Pb i : W.DD T₂ × W.DD T₂).2 ∈ PiNS W T₂ π' M)
    (pr : ↥(W.wachCocyclesDelta T₂)) (hpr1 : (pr : W.DD T₂ × W.DD T₂).1 ∈ InvS W T₂ π' Eπ h' M c)
    (hpr2 : (pr : W.DD T₂ × W.DD T₂).2 ∈ PiNS W T₂ π' M)
    (w₁ : W.DD T₁) (hw₁ : w₁ ∈ InvS W T₁ π' Eπ h' 1 c) (o : Fin r → O)
    (hrel : ((PD.p : ℕ) : O) ^ N • (pr : W.DD T₂ × W.DD T₂).1 - W.map F w₁ - ∑ i, o i • Yb i ∈
      PiNS W T₂ π' 1) :
    ∃ pr₁ : ↥(W.wachCocyclesDelta T₁), (pr₁ : W.DD T₁ × W.DD T₁).1 ∈ InvS W T₁ π' Eπ h' M c ∧
      (pr₁ : W.DD T₁ × W.DD T₁).2 ∈ PiNS W T₁ π' M ∧
      ((PD.p : ℕ) : O) ^ (σ + N) • W.clK T₂ pr =
        LatHom.H1map F (W.clK T₁ pr₁) + ∑ i, o i • W.clK T₂ (Pb i) := by
  obtain ⟨wb, hwbM, hwbR⟩ := hR₁.1 w₁ hw₁
  obtain ⟨z₁, hz₁M, hz₁Z⟩ := hC₁.1 wb hwbM
  have hFZ := univLinkPf_map_Z1DΔ W F hz₁Z
  have hnat : LatHom.H1map F (W.clK T₁ ⟨(wb, z₁), hz₁Z⟩) =
      W.clK T₂ ⟨(W.map F wb, W.map F z₁), hFZ⟩ :=
    hK F ⟨(wb, z₁), hz₁Z⟩ ⟨(W.map F wb, W.map F z₁), hFZ⟩ rfl
  have hE : ((PD.p : ℕ) : O) ^ (σ + N) • (pr : W.DD T₂ × W.DD T₂).1 -
      (W.map F wb + ∑ i, o i • Ybb i) ∈ PiNS W T₂ π' M := by
    apply hR₂.2
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hpr1)
        (Submodule.add_mem _ (univLinkPf_map_InvS W F hc₁ hc₂ π' Eπ h' M c hwbM)
          (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hYbb i)))
    · have e1 := (Submodule.Quotient.mk_eq_zero (PiNS W T₂ π' 1)).2 hrel
      have e2 := (Submodule.Quotient.mk_eq_zero (PiNS W T₂ π' 1)).2
        (univLinkPf_map_PiNS W F hc₁ hc₂ π' 1 hwbR)
      have e3 : ∀ i, (PiNS W T₂ π' 1).mkQ (Ybb i) =
          ((PD.p : ℕ) : O) ^ σ • (PiNS W T₂ π' 1).mkQ (Yb i) := by
        intro i
        have h := (Submodule.Quotient.mk_eq_zero (PiNS W T₂ π' 1)).2 (hYbbR i)
        rw [← Submodule.mkQ_apply, map_sub, map_smul, sub_eq_zero] at h
        exact h.symm
      rw [← Submodule.mkQ_apply] at e1 e2
      simp only [map_sub, map_sum, map_smul] at e1
      rw [sub_sub, sub_eq_zero] at e1
      rw [map_sub, map_sub, univLinkPf_map_osmul, map_smul, sub_eq_zero] at e2
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
      simp only [map_sub, map_add, map_sum, map_smul, e3]
      rw [pow_add, mul_smul, e1, ← e2, smul_add, Finset.smul_sum]
      simp only [smul_smul, mul_comm (((PD.p : ℕ) : O) ^ σ)]
      abel
  let Pc : ↥(W.wachCocyclesDelta T₂) := ⟨(W.map F wb, W.map F z₁), hFZ⟩ + ∑ i, o i • Pb i
  have hPc1 : (Pc : W.DD T₂ × W.DD T₂).1 = W.map F wb + ∑ i, o i • Ybb i := by
    simp only [Pc, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Prod.fst_add, Prod.fst_sum, Prod.smul_fst, hPb1]
  have hPc2 : (Pc : W.DD T₂ × W.DD T₂).2 =
      W.map F z₁ + ∑ i, o i • (Pb i : W.DD T₂ × W.DD T₂).2 := by
    simp only [Pc, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul,
      Prod.snd_add, Prod.snd_sum, Prod.smul_snd]
  have hcl := hC₂.2.1 (((PD.p : ℕ) : O) ^ (σ + N) • pr) Pc
    (by rw [Submodule.coe_smul, Prod.smul_fst]; exact Submodule.smul_mem _ _ hpr1)
    (by rw [Submodule.coe_smul, Prod.smul_snd]; exact Submodule.smul_mem _ _ hpr2)
    (by rw [hPc1]; exact Submodule.add_mem _ (univLinkPf_map_InvS W F hc₁ hc₂ π' Eπ h' M c hwbM)
          (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hYbb i)))
    (by rw [hPc2]; exact Submodule.add_mem _ (univLinkPf_map_PiNS W F hc₁ hc₂ π' M hz₁M)
          (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hPb2 i)))
    (by rw [Submodule.coe_smul, Prod.smul_fst, hPc1]; exact hE)
  refine ⟨⟨(wb, z₁), hz₁Z⟩, hwbM, hz₁M, ?_⟩
  calc ((PD.p : ℕ) : O) ^ (σ + N) • W.clK T₂ pr
        = W.clK T₂ (((PD.p : ℕ) : O) ^ (σ + N) • pr) := (map_smul (W.clK T₂) _ pr).symm
    _ = W.clK T₂ Pc := hcl
    _ = W.clK T₂ ⟨(W.map F wb, W.map F z₁), hFZ⟩ + W.clK T₂ (∑ i, o i • Pb i) :=
        map_add (W.clK T₂) _ _
    _ = LatHom.H1map F (W.clK T₁ ⟨(wb, z₁), hz₁Z⟩) + ∑ i, o i • W.clK T₂ (Pb i) :=
        congrArg₂ (· + ·) hnat.symm ((map_sum (W.clK T₂) _ _).trans
          (Finset.sum_congr rfl fun i _ => map_smul (W.clK T₂) _ _))

theorem univLinkPf_local [StrongRankCondition O] {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (hc₁ : IsCrys PD T₁.ρ) (hc₂ : IsCrys PD T₂.ρ) (hK : W.ClKNat)
    {Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop} {π' Eπ : LetA O n} {h' M σ κ y₁ S η m : ℕ}
    {c : ZMod n} {up : (K →ₐ[Qp] LL) → Bool} {b : (K →ₐ[Qp] LL) → ℕ}
    {α : FrA W π' Eπ h' M c} {β : FrB W π' Eπ h' M c}
    (hβα : ∀ y hy x hx, β T₂ ⟨y, hy⟩ = mkLA W T₂ π' Eπ h' M c x hx →
      α T₂ ⟨x, hx⟩ = mkP W T₂ π' Eπ h' M c (((PD.p : ℕ) : O) ^ (2 * σ) • y)
        ((LamPS W T₂ Eπ h' c).smul_mem _ hy))
    (hMF : ModelF W T₂ Pt π' Eπ h' M c α β) (hM : 1 ≤ M)
    (hR₁ : InvLift W T₁ π' Eπ h' M σ c) (hR₂ : InvLift W T₂ π' Eπ h' M σ c)
    (hC₁ : ClassMap W T₁ π' Eπ h' M c) (hC₂ : ClassMap W T₂ π' Eπ h' M c)
    (hk : KapPi W c S h' κ up b)
    (hU1 : FirstPropositionFrame W F Pt π' Eπ h' M c S η m up b β) (hL : HypL (PD := PD) F S η m h' up b)
    (hU2 : SecondPropositionFree W T₂ Pt π' Eπ h' c)
    (hU3 : ThirdPropositionSlot W F Pt π' Eπ h' M S up b c y₁ α) :
    ∃ s₀ : Finset (G → T₂.V), s₀.card ≤ finrank K₀ K * (finrank K₀ K + 1) * m ∧
      (s₀ : Set (G → T₂.V)) ⊆ latticeFiniteCocycles PD T₂.L ∧
      ∀ x ∈ JZ W T₂ π' Eπ h' M c, ((PD.p : ℕ) : O) ^ (σ + (2 * σ + κ + y₁)) • x ∈
        F.ImF PD ⊔ Submodule.span O (s₀ : Set (G → T₂.V)) := by
  classical
  obtain ⟨u, hu⟩ := hk
  obtain ⟨Lr, k, ell, hell, hrk, hFil, -, hU1w⟩ := hU1 hL
  obtain ⟨hfin, hfree, hrk2⟩ := hU2 Lr
  have := hfin
  have := hfree
  obtain ⟨xb, hxb⟩ := univLinkPf_basis W T₂ Pt π' Eπ h' c Lr
  have hxbL : ∀ i, (xb i : LA W T₂ π' c) ∈ LamLA W T₂ π' Eπ h' c ⊤ := fun i =>
    univLinkPf_LamLA_le W T₂ π' Eπ h' c Lr (Submodule.mem_inf.1 (xb i).2).1
  choose Yb hYb using fun i => Submodule.Quotient.mk_surjective _ (α T₂ ⟨xb i, hxbL i⟩)
  have hYbI : ∀ i, (Yb i : W.DD T₂) ∈ InvS W T₂ π' Eπ h' 1 c := fun i =>
    hMF.2.2.2.1 _ (hxbL i) _ (Yb i).2 (hYb i).symm
      (univLinkPf_InvL_le W T₂ Pt π' Eπ h' c Lr (xb i).2)
  choose Ybb hYbb hYbbR using fun i => hR₂.1 _ (hYbI i)
  choose zb hzb hzbZ using fun i => hC₂.1 _ (hYbb i)
  let Pb : Fin (finrank O (IIrest W T₂ Pt π' Eπ h' c Lr)) → ↥(W.wachCocyclesDelta T₂) :=
    fun i => ⟨(Ybb i, zb i), hzbZ i⟩
  choose κb hκbf hκbZ hκbcl using fun i => hC₂.2.2 (Pb i) (hYbb i) (hzb i)
  refine ⟨Finset.univ.image κb, ?_, ?_, ?_⟩
  · calc (Finset.univ.image κb).card ≤ Finset.univ.card := Finset.card_image_le
      _ = finrank O (IIrest W T₂ Pt π' Eπ h' c Lr) := by simp
      _ ≤ (finrank K₀ K + 1) * finrank O Lr := hrk2
      _ ≤ (finrank K₀ K + 1) * (finrank K₀ K * m) := Nat.mul_le_mul_left _ hrk
      _ = finrank K₀ K * (finrank K₀ K + 1) * m := by ring
  · intro κ' hκ'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hκ')
    exact hκbf i
  · intro x hx
    unfold JZ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨hκ, w, hwM, z, hzM, hwz, hcl⟩ := hy
      have hw1 := univLinkPf_InvS_anti W T₂ π' Eπ h' c hM hwM
      obtain ⟨w₁, hw₁, o, hrel⟩ := univLinkPf_cong W F hβα hMF hM u hu hU3 Lr ell hell hFil xb hxb
        hxbL Yb (fun i => (hYb i).symm) w hw1 (hU1w w hw1)
      obtain ⟨pr₁, hp1, hp2, heq⟩ := univLinkPf_class W F hc₁ hc₂ hK hR₁ hR₂ hC₁ hC₂
        (fun i => (Yb i : W.DD T₂)) Ybb hYbb hYbbR Pb (fun i => rfl) hzb ⟨(w, z), hwz⟩ hwM hzM
        w₁ hw₁ o hrel
      obtain ⟨κ₁, hκ₁f, hκ₁Z, hκ₁cl⟩ := hC₁.2.2 pr₁ hp1 hp2
      have hZ : ((PD.p : ℕ) : O) ^ (σ + (2 * σ + κ + y₁)) • (⟨y, hκ⟩ : ↥(latticeCocycles T₂.L)) -
          ⟨F.post κ₁, F.post_Z1T κ₁ hκ₁Z⟩ - ∑ i, o i • (⟨κb i, hκbZ i⟩ : ↥(latticeCocycles T₂.L)) ∈
          (latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype := by
        have h1 : Submodule.mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype) (⟨y, hκ⟩ : ↥(latticeCocycles T₂.L)) =
            W.clK T₂ ⟨(w, z), hwz⟩ := hcl
        have h2 : Submodule.mkQ ((latticeCoboundaries T₂.L).comap (latticeCocycles T₂.L).subtype)
            (⟨F.post κ₁, F.post_Z1T κ₁ hκ₁Z⟩ : ↥(latticeCocycles T₂.L)) = LatHom.H1map F (W.clK T₁ pr₁) := by
          rw [← hκ₁cl]; rfl
        rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
        simp only [map_sub, map_sum, map_smul]
        rw [h1, h2, sub_sub, sub_eq_zero]
        exact heq.trans (congrArg (LatHom.H1map F (W.clK T₁ pr₁) + ·)
          (Finset.sum_congr rfl fun i _ => congrArg (o i • ·) (hκbcl i).symm))
      have hB := Submodule.mem_comap.1 hZ
      simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_smul,
        Submodule.coe_sum, Submodule.coe_mk] at hB
      have hImF : F.post κ₁ ∈ F.ImF PD := by
        unfold LatHom.ImF; exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hκ₁f)
      have hBI : ((PD.p : ℕ) : O) ^ (σ + (2 * σ + κ + y₁)) • y - F.post κ₁ -
          ∑ i, o i • κb i ∈ F.ImF PD := by
        unfold LatHom.ImF; exact Submodule.mem_sup_right hB
      have hsp : ∑ i, o i • κb i ∈ Submodule.span O (↑(Finset.univ.image κb) : Set (G → T₂.V)) :=
        Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      have hall := Submodule.add_mem _
        (Submodule.mem_sup_left (Submodule.add_mem _ hImF hBI) :
          _ ∈ F.ImF PD ⊔ Submodule.span O (↑(Finset.univ.image κb) : Set (G → T₂.V)))
        (Submodule.mem_sup_right hsp :
          _ ∈ F.ImF PD ⊔ Submodule.span O (↑(Finset.univ.image κb) : Set (G → T₂.V)))
      convert hall using 1
      abel
    | zero => rw [smul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [smul_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [smul_comm]; exact Submodule.smul_mem _ a hy

end Local

end Formalism.MainNotions.N.Ln34.UnivLinkPf

end
