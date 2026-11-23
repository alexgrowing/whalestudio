import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import GroundTheory.AutomorphicForms.SmoothRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriBlockUpperLeviLower
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenIsCompactPrincipal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeFunctionConstantTermVanishSplitPlace

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.HeckeJacquet

open GroundTheory.Automorphic in

theorem sub_mem_of_invariant_forms {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (hρ : GroundTheory.Automorphic.IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (P : Submodule ℂ V) (w t : V)
    (hw : ∀ x ∈ K, ρ x w - w ∈ P) (ht : t ∈ fixedVectors ρ K)
    (hl : ∀ l : Module.Dual ℂ V, (∀ x ∈ K, l ∘ₗ ρ x = l) → l w = l t) : t - w ∈ P := by
  obtain ⟨Nn, -, hNK, hNU, hnorm, hfin⟩ := exists_normal_subgroup hKc hKo ((hρ w).mem_nhds
    (one_mem (stabilizerOf ρ w)))
  have := Fintype.ofFinite (K ⧸ Nn.subgroupOf K)
  have hwN : w ∈ fixedVectors ρ Nn := fun n hn => hNU hn
  set n : ℂ := (Fintype.card (K ⧸ Nn.subgroupOf K) : ℂ) with hn_def
  have hn : n ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  set u : V := n⁻¹ • cosetSum ρ K Nn w with hu_def
  have huK : u ∈ fixedVectors ρ K :=
    Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hwN)
  have heq : w - u = n⁻¹ • ∑ q : K ⧸ Nn.subgroupOf K, (w - ρ ((Quotient.out q : K) : G) w) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ← cosetSum_apply, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hn, one_smul]
  have hcoinv : w - u ∈ coinvariantsKer ρ K := by
    rw [heq]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    rw [← neg_sub]
    exact Submodule.neg_mem _ (sub_mem_coinvariantsKer (Quotient.out q).2 w)
  have hP : w - u ∈ P := by
    rw [heq]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_)
    rw [← neg_sub]
    exact Submodule.neg_mem _ (hw _ (Quotient.out q).2)
  have hproj : fixedProj ρ hρ hKc hKo w = ⟨u, huK⟩ := (fixedProj_eq_iff hρ hKc hKo).2 hcoinv
  have hprojt : fixedProj ρ hρ hKc hKo t = ⟨t, ht⟩ :=
    Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo ht)
  have hut : (⟨u, huK⟩ : fixedVectors ρ K) = ⟨t, ht⟩ := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro f
    have h := hl (f ∘ₗ fixedProj ρ hρ hKc hKo) (fun x hx => by
      ext y
      simp only [LinearMap.comp_apply, fixedProj_apply_act hρ hKc hKo hx])
    simp only [LinearMap.comp_apply, hproj, hprojt] at h
    rw [map_sub, h, sub_self]
  have hutv : u = t := congrArg Subtype.val hut
  rw [← hutv]
  have := Submodule.neg_mem _ hP
  rwa [neg_sub] at this

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem totallyDisconnected_GL (N : ℕ) : TotallyDisconnectedSpace (GL (Fin N) k) := by
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  exact ⟨isTotallyDisconnected_of_image (f := fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k))
    Units.continuous_val.continuousOn Units.val_injective
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

variable (k) in

theorem val_unif_lt_one : valuation k ((Zls.unifU k : kˣ) : k) < 1 := by
  have hle : valuation k ((Zls.unif k : 𝒪[k]) : k) ≤ 1 := (Zls.unif k).2
  refine lt_of_le_of_ne hle fun h1 => (Zls.irreducible_unif (k := k)).not_isUnit ?_
  exact ((Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one).2 h1

variable (k) in

theorem val_le_unif (x : k) (hx : valuation k x < 1) :
    valuation k x ≤ valuation k ((Zls.unifU k : kˣ) : k) := by
  have hint := Valuation.integer.integers (valuation k)
  let y : 𝒪[k] := ⟨x, hx.le⟩
  have hy : y ∈ IsLocalRing.maximalIdeal 𝒪[k] := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact hx.ne (hint.isUnit_iff_valuation_eq_one.1 hu)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 Zls.irreducible_unif,
    Ideal.mem_span_singleton] at hy
  exact hint.le_of_dvd hy

theorem mem_Km_iff (N : ℕ) {m : ℕ} (hm : 1 ≤ m) (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
      (1 : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (((Zls.unifU k : kˣ) : k) ^ m) := by
  have ht0 : (((Zls.unifU k : kˣ) : k) ^ m) ≠ 0 := pow_ne_zero _ (Zls.unifU k).ne_zero
  have hint := Valuation.integer.integers (valuation k)
  have htlt : valuation k (((Zls.unifU k : kˣ) : k) ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' (val_unif_lt_one k) (by omega)
  have hcoe : ((Zls.unifU k : kˣ) : k) = ((Zls.unif k : 𝒪[k]) : k) := rfl
  constructor
  · rintro ⟨h, hker, rfl⟩
    intro i j
    have hk := congrArg (fun u : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) =>
      u.1 i j) (MonoidHom.mem_ker.1 hker)
    have hk' : Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})
        ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j) =
        Ideal.Quotient.mk (Ideal.span {Zls.unif k ^ m})
          ((1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) := by
      by_cases hij : i = j
      · subst hij
        simpa using hk
      · simpa [Matrix.one_apply_ne hij] using hk
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at hk'
    have h2 := hint.le_of_dvd hk'
    have e1 : ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) h : GL (Fin N) k) :
        Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j =
        algebraMap 𝒪[k] k ((h : Matrix (Fin N) (Fin N) 𝒪[k]) i j -
          (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) := by
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.one_apply_ne hij]
    have e2 : algebraMap 𝒪[k] k (Zls.unif k ^ m) = ((Zls.unifU k : kˣ) : k) ^ m := by
      rw [map_pow]
      rfl
    rw [e1, ← e2]
    exact h2
  · intro hg
    have hginv := GlobalTheory.CompanionTheory.PrincipalCongruence.inv_congr (g : Matrix (Fin N) (Fin N) k)
      ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) (by simp) htlt hg
    have hone : ∀ i j, valuation k ((1 : Matrix (Fin N) (Fin N) k) i j) ≤ 1 := by
      intro i j
      by_cases h : i = j
      · subst h
        simp
      · simp [Matrix.one_apply_ne h]
    have hent : ∀ (A : Matrix (Fin N) (Fin N) k), (∀ i j, valuation k (A i j -
        (1 : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (((Zls.unifU k : kˣ) : k) ^ m)) →
        ∀ i j, valuation k (A i j) ≤ 1 := by
      intro A hA i j
      have := Valuation.map_add_le (valuation k) ((hA i j).trans htlt.le) (hone i j)
      simpa using this
    let A : Matrix (Fin N) (Fin N) 𝒪[k] := fun i j => ⟨_, hent _ hg i j⟩
    let B : Matrix (Fin N) (Fin N) 𝒪[k] := fun i j => ⟨_, hent _ hginv i j⟩
    have hAm : A.map (algebraMap 𝒪[k] k) = (g : Matrix (Fin N) (Fin N) k) := rfl
    have hBm : B.map (algebraMap 𝒪[k] k) = ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) := rfl
    have hinj : Function.Injective (fun M : Matrix (Fin N) (Fin N) 𝒪[k] => M.map (algebraMap 𝒪[k] k)) :=
      Matrix.map_injective (IsFractionRing.injective 𝒪[k] k)
    have hAB : A * B = 1 := hinj (by
      show (A * B).map (algebraMap 𝒪[k] k) = (1 : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k)
      rw [Matrix.map_mul, hAm, hBm, Matrix.map_one _ (map_zero _) (map_one _)]
      simp)
    have hBA : B * A = 1 := hinj (by
      show (B * A).map (algebraMap 𝒪[k] k) = (1 : Matrix (Fin N) (Fin N) 𝒪[k]).map (algebraMap 𝒪[k] k)
      rw [Matrix.map_mul, hAm, hBm, Matrix.map_one _ (map_zero _) (map_one _)]
      simp)
    refine ⟨⟨A, B, hAB, hBA⟩, ?_, Units.ext hAm⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    refine Units.ext (Matrix.ext fun i j => ?_)
    have hdv : Zls.unif k ^ m ∣ A i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j := by
      refine hint.le_iff_dvd.1 ?_
      have e1 : algebraMap 𝒪[k] k (A i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j) =
          (g : Matrix (Fin N) (Fin N) k) i j - (1 : Matrix (Fin N) (Fin N) k) i j := by
        have e0 : algebraMap 𝒪[k] k (A i j) = (g : Matrix (Fin N) (Fin N) k) i j := rfl
        rw [map_sub, e0]
        by_cases hij : i = j
        · subst hij
          simp
        · simp [Matrix.one_apply_ne hij]
      have e2 : algebraMap 𝒪[k] k (Zls.unif k ^ m) = ((Zls.unifU k : kˣ) : k) ^ m := by
        rw [map_pow]
        rfl
      rw [e1, e2]
      exact hg i j
    have hq := (Ideal.Quotient.eq (I := Ideal.span {Zls.unif k ^ m})).2
      (Ideal.mem_span_singleton.2 hdv)
    by_cases hij : i = j
    · subst hij
      simpa using hq
    · simpa [Matrix.one_apply_ne hij] using hq

theorem coe_diagPow (N : ℕ) (lam : Fin N → ℤ) :
    ((Zls.diagPow k N lam : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ lam i : kˣ) : k) := rfl

theorem coe_diagPow_inv (N : ℕ) (lam : Fin N → ℤ) :
    (((Zls.diagPow k N lam)⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun i => ((Zls.unifU k ^ (-lam i) : kˣ) : k) := by
  have h : Zls.diagPow k N lam * Zls.diagPow k N (fun i => -lam i) = 1 := by
    refine Units.ext ?_
    rw [Units.val_mul, coe_diagPow, coe_diagPow, Matrix.diagonal_mul_diagonal, Units.val_one,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  rw [← eq_inv_of_mul_eq_one_right h, coe_diagPow]

theorem conj_mem_Km {N m : ℕ} (hm : 1 ≤ m) (a : ℕ) {z : GL (Fin N) k} (hz : z ∈ Zls.Km k N m)
    (h0 : ∀ i j : Fin N, (i : ℕ) < a → a ≤ (j : ℕ) → (z : Matrix (Fin N) (Fin N) k) i j = 0) :
    (Zls.diagPow k N (Zls.omegaVec N a))⁻¹ * z * Zls.diagPow k N (Zls.omegaVec N a) ∈
      Zls.Km k N m := by
  rw [mem_Km_iff N hm] at hz ⊢
  intro i j
  have hent : (((Zls.diagPow k N (Zls.omegaVec N a))⁻¹ * z * Zls.diagPow k N (Zls.omegaVec N a) :
      GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j =
      ((Zls.unifU k ^ (-(Zls.omegaVec N a i)) : kˣ) : k) * (z : Matrix (Fin N) (Fin N) k) i j *
        ((Zls.unifU k ^ (Zls.omegaVec N a j) : kˣ) : k) := by
    rw [Units.val_mul, Units.val_mul, coe_diagPow_inv, coe_diagPow, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
  rw [hent]
  have hu : ((Zls.unifU k : kˣ) : k) ≠ 0 := (Zls.unifU k).ne_zero
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a
  · have e : ((Zls.unifU k ^ (-(Zls.omegaVec N a i)) : kˣ) : k) * (z : Matrix (Fin N) (Fin N) k) i j *
        ((Zls.unifU k ^ (Zls.omegaVec N a j) : kˣ) : k) = (z : Matrix (Fin N) (Fin N) k) i j := by
      simp only [Zls.omegaVec, hi, hj, if_true, zpow_neg_one, zpow_one, Units.val_inv_eq_inv_val]
      field_simp
    rw [e]
    exact hz i j
  · have hne : i ≠ j := fun h => hj (h ▸ hi)
    rw [h0 i j hi (not_lt.1 hj), Matrix.one_apply_ne hne]
    simp
  · have hne : i ≠ j := fun h => hi (h ▸ hj)
    have e : ((Zls.unifU k ^ (-(Zls.omegaVec N a i)) : kˣ) : k) * (z : Matrix (Fin N) (Fin N) k) i j *
        ((Zls.unifU k ^ (Zls.omegaVec N a j) : kˣ) : k) =
        (z : Matrix (Fin N) (Fin N) k) i j * ((Zls.unifU k : kˣ) : k) := by
      simp [Zls.omegaVec, hi, hj]
    rw [e, Matrix.one_apply_ne hne, sub_zero, map_mul]
    have h1 := hz i j
    rw [Matrix.one_apply_ne hne, sub_zero] at h1
    calc _ ≤ valuation k (((Zls.unifU k : kˣ) : k) ^ m) * 1 :=
          mul_le_mul' h1 (val_unif_lt_one k).le
      _ = _ := mul_one _
  · have e : ((Zls.unifU k ^ (-(Zls.omegaVec N a i)) : kˣ) : k) * (z : Matrix (Fin N) (Fin N) k) i j *
        ((Zls.unifU k ^ (Zls.omegaVec N a j) : kˣ) : k) = (z : Matrix (Fin N) (Fin N) k) i j := by
      simp [Zls.omegaVec, hi, hj]
    rw [e]
    exact hz i j

theorem mem_unipRad_of_entries {N : ℕ} (d : Fin 2 → ℕ) (hd : ∑ a, d a = N) {g : GL (Fin N) k}
    (h : ∀ i j : Fin N, (g : Matrix (Fin N) (Fin N) k) i j ≠ (1 : Matrix (Fin N) (Fin N) k) i j →
      (i : ℕ) < d 0 ∧ d 0 ≤ (j : ℕ)) :
    g ∈ unipRad k (stdBlocks d hd) := by
  obtain ⟨a, b, rfl⟩ : ∃ a b, d = ![a, b] := ⟨d 0, d 1, by ext i; fin_cases i <;> rfl⟩
  exact (GlobalTheory.TypeConstLoc.mem_unipRad_stdBlocks_iff hd).2 h

end

theorem hecke_omega_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → ∀ m : ℕ, 1 ≤ m → ∀ (d : Fin 2 → ℕ) (hd : ∑ a, d a = N), 0 < d 0 → 0 < d 1 → ∀ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T → ∀ v : fixed π (Zls.Km k N m), (Submodule.Quotient.mk ((T v : fixed π (Zls.Km k N m)) : V) : Jacquet π (unipRad k (stdBlocks d hd))) = Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (v : V)) := by
  intro k _ _ _ _ N V _ _ π hπ m hm d hd hd0 hd1 T hT v
  haveI := totallyDisconnected_GL (k := k) N
  haveI : LocallyCompactSpace (GL (Fin N) k) := GlobalTheory.SplitFlip.locallyCompact_GL
  have ht0 : (((Zls.unifU k : kˣ) : k) ^ m) ≠ 0 := pow_ne_zero _ (Zls.unifU k).ne_zero
  have htlt : valuation k (((Zls.unifU k : kˣ) : k) ^ m) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' (val_unif_lt_one k) (by omega)
  have hset : (Zls.Km k N m : Set (GL (Fin N) k)) =
      {g : GL (Fin N) k | ∀ i j, valuation k ((g : Matrix (Fin N) (Fin N) k) i j -
        (1 : Matrix (Fin N) (Fin N) k) i j) ≤ valuation k (((Zls.unifU k : kˣ) : k) ^ m)} :=
    Set.ext (mem_Km_iff N hm)
  obtain ⟨hKo, hKc⟩ := GlobalTheory.CompanionTheory.PrincipalCongruence.isOpen_isCompact_principal k N _ ht0 htlt
  rw [← hset] at hKo hKc
  have hfix : ∀ (u : fixed π (Zls.Km k N m)), ∀ x ∈ Zls.Km k N m, π x (u : V) = u := by
    intro u x hx
    simpa using u.2 ⟨x, hx⟩
  set D := Zls.diagPow k N (Zls.omegaVec N (d 0)) with hD
  have hmove : ∀ x ∈ Zls.Km k N m, π x (π D (v : V)) - π D (v : V) ∈
      twKer π (unipRad k (stdBlocks d hd)) 1 := by
    intro x hx
    let β : Fin N → ℕ := fun i => if (i : ℕ) < d 0 then 0 else 1
    have hβ : Monotone β := by
      intro i j hij
      have hij' : (i : ℕ) ≤ j := hij
      simp only [β]
      split_ifs <;> omega
    obtain ⟨nm, hnm, l, hl, np, hnp, h1, h2, h3, rfl⟩ :=
      GlobalTheory.CompanionTheory.BlockIwahoriUML.iwahori_block_upper_levi_lower k N ((Zls.unifU k : kˣ) : k) m β
        (Zls.unifU k).ne_zero (val_unif_lt_one k) (val_le_unif k) hm hβ x
        ((mem_Km_iff N hm x).1 hx)
    have hnm' : nm ∈ Zls.Km k N m := (mem_Km_iff N hm nm).2 hnm
    have hl' : l ∈ Zls.Km k N m := (mem_Km_iff N hm l).2 hl
    have hU : np ∈ unipRad k (stdBlocks d hd) := by
      refine mem_unipRad_of_entries d hd fun i j hij => ?_
      by_contra hcon
      refine hij (h3 i j ?_)
      simp only [β]
      split_ifs <;> omega
    have hz1 := conj_mem_Km hm (d 0) hl' (fun i j hi hj => h2 i j (by
      simp only [β]
      split_ifs <;> omega))
    have hz2 := conj_mem_Km hm (d 0) hnm' (fun i j hi hj => by
      have hne : i ≠ j := fun h => by
        rw [h] at hi
        omega
      rw [h1 i j (by
        simp only [β]
        split_ifs <;> omega), Matrix.one_apply_ne hne])
    rw [← hD] at hz1 hz2
    have hmul : l * nm * D = D * (D⁻¹ * l * D) * (D⁻¹ * nm * D) := by group
    have key : π (l * nm) (π D (v : V)) = π D (v : V) := by
      rw [← Module.End.mul_apply, ← map_mul, hmul, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, hfix v _ hz2, hfix v _ hz1]
    have hsplit : π (np * l * nm) (π D (v : V)) = π np (π D (v : V)) := by
      rw [mul_assoc, map_mul, Module.End.mul_apply, key]
    rw [hsplit]
    exact Submodule.subset_span ⟨⟨np, hU⟩, π D (v : V), by simp⟩
  refine (Submodule.Quotient.eq _).2 (sub_mem_of_invariant_forms π (fun u => hπ u) hKc hKo _ _ _ hmove
    (fun x hx => hfix (T v) x hx) (fun l hl => hT v l hl))

end GlobalTheory.CompanionTheory.HeckeJacquet
