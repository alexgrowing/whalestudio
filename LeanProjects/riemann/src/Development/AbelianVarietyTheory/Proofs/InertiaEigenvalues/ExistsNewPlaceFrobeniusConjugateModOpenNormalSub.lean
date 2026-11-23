import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAuxiliaryPrimesPrescribedFrobenius

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate
open GlobalTheory.ChosenPrimes

namespace GlobalTheory.NewPrimePick

theorem exists_newPlace : Cheb → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (i : X.Tw) (s : X.Sig i), ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → n < R → ∀ (H : Subgroup (GE N)) (S : Finset (PlE D.host)), AdmFam X i M H S d → L ≤ H → ∀ (U : Subgroup (GE N)) (h : GE N), IsOpen (U : Set (GE N)) → U.Normal → U ≤ L → h ∈ L → (∀ b : Fin R, b.val < n → d (P (.inl b)) h = 1) → (∀ b : Fin R, n ≤ b.val → Ine (F := D.host.E) (N.plOm.1 (P (.inl b))) ≤ U) → ∃ P' : Fin R ⊕ Fin (n + 1) → PlE D.host, Ext P P' ∧ PiLocalization₂ i M d A₀ L z P' ∧ ∃ σ γ g : GE N, NewPl i M L (P' (.inr (Fin.last n))) (d (P' (.inr (Fin.last n)))) σ γ ∧ d (P' (.inr (Fin.last n))) σ = 1 ∧ g * σ * g⁻¹ * h⁻¹ ∈ U := by
  intro hC D N X i s M R n d A L z P _ _ hsm hst _ H S hA hLH U h hU hUn hUL hh hh1 hIU
  classical
  obtain ⟨-, -, -, hd⟩ := hA
  obtain ⟨⟨hL, hLn, -⟩, hLr, -⟩ := hsm
  obtain ⟨⟨ha1, ha2, ha3⟩, hs1, hs2⟩ := hst
  have hl := (X.lPrime i).out
  set m := 2 * X.l i ^ M with hm
  have hn1 : 1 < m := by have := Nat.pow_pos (n := M) hl.pos; omega
  have hn0 : m ≠ 0 := by omega
  have hval := exists_values (U ⊓ ⨅ b : {b : Fin R // b.val < n}, (d (P (.inl b.1))).ker)
    (fun b : {b : Fin R // n ≤ b.val} => d (P (.inl b.1))) (fun b c => by
      obtain ⟨γ, hγ, e⟩ := (ha3 (.inl b.1)).2.2.2.2 _ (over_refl _) _ (N.plOm.2 (P (.inl b.1))) c
      have key : ∀ b' : Fin R, b' ≠ b.1 → d (P (.inl b')) γ = 1 := fun b' hb' =>
        (ha3 (.inl b')).2.2.2.1 _ (fun h => hb' (Sum.inl_injective (ha2 _ _ h))) _ (N.plOm.2 (P (.inl b.1))) γ hγ
      refine ⟨γ, ⟨hIU b.1 b.2 hγ, Subgroup.mem_iInf.2 fun b' => key b'.1 fun h => ?_⟩, e,
        fun b' hb' => key b'.1 fun h => hb' (Subtype.ext h)⟩
      have h1 := b'.2
      have h2 := b.2
      rw [h] at h1
      omega)
  obtain ⟨γ₀, hγ₀, hγd⟩ := hval fun b =>
    Multiplicative.ofAdd (if n = b.1.val then 1 else 0) * (d (P (.inl b.1)) h)⁻¹
  have hγh : ∀ b : Fin R, d (P (.inl b)) (γ₀ * h) = Multiplicative.ofAdd (if n = b.val then 1 else 0) := by
    intro b
    rw [map_mul]
    rcases lt_or_ge b.val n with hb | hb
    · have h1 : d (P (.inl b)) γ₀ = 1 := Subgroup.mem_iInf.1 hγ₀.2 ⟨b, hb⟩
      rw [h1, hh1 b hb, if_neg (by omega), mul_one]
      rfl
    · rw [hγd ⟨b, hb⟩, inv_mul_cancel_right]
  let V : Subgroup (GE N) := U ⊓ ⨅ b, (d (P (.inl b))).ker
  have hV : IsOpen (V : Set (GE N)) := by
    refine hU.inter ?_
    show IsOpen ((⨅ b, (d (P (.inl b))).ker : Subgroup (GE N)) : Set (GE N))
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun b => (ha3 (.inl b)).1
  have hVn : V.Normal := by
    have : (⨅ b, (d (P (.inl b))).ker).Normal := Subgroup.normal_iInf_normal fun b => inferInstance
    infer_instance
  obtain ⟨T₀, hT₀, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split D.host
  let T : Set (PlE D.host) := ((↑A ∪ ↑S ∪ ↑(X.S0 i)) ∪ (T₀ ∪ {P | P.asIdeal.ramificationIdx ℤ ≠ 1}) ∪
    ({v | ((m : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal} ∪
      {v | ∃ B : ValuationSubring N.Om, IsPlaceOver B v ∧ ¬ Ine (F := D.host.E) B ≤ U})) ∪ Set.range P
  have hT : T.Finite :=
    ((((A.finite_toSet.union S.finite_toSet).union (X.S0 i).finite_toSet).union
      (hT₀.union (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified D.host.E).2)).union
      ((finite_mem hn0).union (finite_ram hU))).union (Set.finite_range P)
  obtain ⟨p, hp⟩ := exists_pick hC hV hVn (γ₀ * h) hT
  have h1 : ∀ v, Over p v → ((((v ∉ A ∧ v ∉ S) ∧ v ∉ X.S0 i) ∧ v ∉ T₀ ∧ v.asIdeal.ramificationIdx ℤ = 1) ∧
      ((m : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal ∧
      ∀ B : ValuationSubring N.Om, IsPlaceOver B v → Ine (F := D.host.E) B ≤ U) ∧ v ∉ Set.range P := fun v hv => by
    have : v ∉ T := (hp.1 v hv).1
    simpa only [T, Set.mem_union, not_or, Finset.mem_coe, Set.mem_ofPred_eq, not_exists, not_and, not_not] using this
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 p)
  obtain ⟨k, hk⟩ := hp.2 σ hσ
  have hσL : σ ∈ L := by
    have h2 := hLn.conj_mem _ (L.mul_mem (hUL hk.1) (L.mul_mem (hUL hγ₀.1) hh)) k⁻¹
    have e : k⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹ * (γ₀ * h)) * k⁻¹⁻¹ = σ := by group
    rwa [e] at h2
  have hP0 := h1 p (over_refl p)
  have hq := norm_mod (N.plOm.2 p) hn1 hP0.1.2.1 hσ (hLr σ hσL)
  have hIp : Ine (F := D.host.E) (N.plOm.1 p) ≤ U := hP0.1.2.2 _ (N.plOm.2 p)
  have hdec : DecV N p ≤ L := dec_le (N.plOm.2 p) hL (hIp.trans hUL) hσ hσL
  have hspl : IsSplitPl D.host p := hsp p hP0.1.1.2.1 (hp.1 p (over_refl p)).2
  have hgood : GoodChar X i M p (d p) := hd p hP0.1.1.1.1.2 hspl (hdec.trans hLH)
  have haux : ∀ v, Over p v → IsSplitPl D.host v ∧ v.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL D.host.E v = 1 ∧
      v ∉ X.S0 i ∧ v ∉ A ∧ normV v % m = 1 := by
    refine fun v hv => ⟨hsp v (h1 v hv).1.1.2.1 (hp.1 v hv).2, (hp.1 v hv).2, (h1 v hv).1.1.2.2, (h1 v hv).1.1.1.2,
      (h1 v hv).1.1.1.1.1, ?_⟩
    rcases hv with rfl | hv
    · exact hq
    · rwa [normV_conj hv]
  let P' : Fin R ⊕ Fin (n + 1) → PlE D.host :=
    Sum.elim (fun a => P (.inl a)) (Fin.snoc (α := fun _ => PlE D.host) (fun a => P (.inr a)) p)
  have e1 : P' (.inr (Fin.last n)) = p := by simp [P']
  have e2 : ∀ q, P' (Sum.map id Fin.castSucc q) = P q := by
    rintro (a | a) <;> simp [P']
  have cases : ∀ q : Fin R ⊕ Fin (n + 1), q = .inr (Fin.last n) ∨ ∃ q₀, q = Sum.map id Fin.castSucc q₀ := by
    rintro (a | a)
    · exact Or.inr ⟨.inl a, rfl⟩
    · refine Fin.lastCases (Or.inl rfl) (fun a => Or.inr ⟨.inr a, rfl⟩) a
  refine ⟨P', e2, ⟨⟨fun q => ?_, fun q q' => ?_, fun q => ?_⟩, hs1, fun a => ?_⟩, ?_⟩
  · rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact haux
    · rw [e2]; exact ha1 q
  · rcases cases q with rfl | ⟨q, rfl⟩ <;> rcases cases q' with rfl | ⟨q', rfl⟩
    · exact fun _ => rfl
    · rw [e1, e2]; exact fun h => ((h1 _ h).2 ⟨q', rfl⟩).elim
    · rw [e1, e2]; exact fun h => ((h1 _ (over_symm h)).2 ⟨q, rfl⟩).elim
    · rw [e2, e2]; exact fun h => by rw [ha2 _ _ h]
  · show GoodChar X i M (P' q) (d (P' q))
    rcases cases q with rfl | ⟨q, rfl⟩
    · rw [e1]; exact hgood
    · rw [e2]; exact ha3 q
  · refine Fin.lastCases ?_ (fun a => ?_) a
    · rw [e1]
      refine ⟨hdec, fun b τ hτ => ?_⟩
      obtain ⟨k', hk'⟩ := hp.2 τ hτ
      have h2 : d (P (.inl b)) _ = 1 := Subgroup.mem_iInf.1 hk'.2 b
      rw [map_mul, map_inv, hγh] at h2
      simp only [map_mul, map_inv, mul_inv_cancel_comm, mul_inv_eq_one] at h2
      exact h2
    · have e3 : P' (.inr a.castSucc) = P (.inr a) := e2 (.inr a)
      rw [e3]
      exact hs2 a
  · rw [e1]
    obtain ⟨γ, hγ, hγ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (Multiplicative.ofAdd 1)
    obtain ⟨τ, hτ, hτ1⟩ := hgood.2.2.2.2 p (over_refl p) _ (N.plOm.2 p) (d p σ)⁻¹
    refine ⟨σ * τ, γ, k, ⟨fun v hv => (haux v hv).2.2.2.1, hspl, hq, hdec, hgood.1, ?_, hγ, hγ1⟩, ?_, ?_⟩
    · first | exact isFrob_mul_of_mem_Ine hσ hτ | exact isFrob_mul_of_mem_Ine hτ hσ
    · rw [map_mul, hτ1, mul_inv_cancel]
    · have h2 := U.mul_mem (U.mul_mem (hUn.conj_mem _ (hIp hτ) (k * σ)) hk.1) hγ₀.1
      have e : k * σ * τ * (k * σ)⁻¹ * (k * σ * k⁻¹ * (γ₀ * h)⁻¹) * γ₀ = k * (σ * τ) * k⁻¹ * h⁻¹ := by group
      rwa [e] at h2

end GlobalTheory.NewPrimePick
