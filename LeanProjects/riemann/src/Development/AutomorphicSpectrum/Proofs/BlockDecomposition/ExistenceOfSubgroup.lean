import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Formalism.SharpRestriction.LevelLetterCocycles.WildPro
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTameGenAtOfValuationSubring
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaTypePrimesOfAdmissible

noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.WeilDeligne LocalGlobalAboveLAlt

namespace GlobalTheory.CompanionTheory.ExSubLeaf

theorem exists_prime_val_lt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) :
    ∃ p : ℕ, p.Prime ∧ A.valuation ((p : ℕ) : Ω) < 1 := by
  haveI : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  haveI := w.isPrime
  haveI : IsDomain (𝓞 E ⧸ w.asIdeal) := Ideal.Quotient.isDomain _
  obtain ⟨p, hc⟩ := CharP.exists (𝓞 E ⧸ w.asIdeal)
  have hp : p.Prime := CharP.char_is_prime (𝓞 E ⧸ w.asIdeal) p
  refine ⟨p, hp, ?_⟩
  have h1 : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero (𝓞 E ⧸ w.asIdeal) p
  have h2 := (h _).mpr h1
  simpa using h2

def wildSub {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω) : Subgroup (G E Ω) where
  carrier := {σ | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}
  one_mem' := Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.one
  mul_mem' := fun ha hb => Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.mul ha hb
  inv_mem' := by
    intro σ hσ y hy
    have hz : (σ⁻¹ : G E Ω) y ≠ 0 := (_root_.map_ne_zero _).mpr hy
    have hy' : σ ((σ⁻¹ : G E Ω) y) = y := mul_inv_apply y
    have h1 := hσ _ hz
    have h2 : A.valuation (y / (σ⁻¹ : G E Ω) y) = 1 := by
      have := Formalism.MainNotions.N.KillingConditions.WildPf.IsWild.val_div (A := A) (σ := σ) hσ hz
      rwa [hy'] at this
    rw [hy'] at h1
    have e : (σ⁻¹ : G E Ω) y / y - 1 = -((y / (σ⁻¹ : G E Ω) y - 1) * ((y / (σ⁻¹ : G E Ω) y)⁻¹)) := by
      field_simp
      ring
    rw [e, Valuation.map_neg, map_mul, map_inv₀, h2, inv_one, mul_one]
    exact h1

theorem conj_mem_wildSub {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    {A : ValuationSubring Ω} {g σ : G E Ω} (hg : g ∈ Dec (F := E) A) (hσ : σ ∈ wildSub (E := E) A) :
    g * σ * g⁻¹ ∈ wildSub (E := E) A := by
  intro y hy
  have hu : (g⁻¹ : G E Ω) y ≠ 0 := (_root_.map_ne_zero _).mpr hy
  have e : (g * σ * g⁻¹) y / y - 1 = g (σ ((g⁻¹ : G E Ω) y) / (g⁻¹ : G E Ω) y - 1) := by
    rw [map_sub, map_div₀, map_one, mul_inv_apply]
    rfl
  rw [e, valuation_apply_lt_one_iff hg]
  exact hσ _ hu

theorem isSolvable_ine_quot {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    (K : Subgroup ↥(Ine (F := E) A)) [K.Normal] (hK : IsOpen (K : Set ↥(Ine (F := E) A))) :
    Group.IsSolvable (↥(Ine (F := E) A) ⧸ K) := by
  classical
  have hgal : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  haveI := compactSpace_Ine (E := E) A
  haveI hQfin : Finite (↥(Ine (F := E) A) ⧸ K) := Subgroup.quotient_finite_of_isOpen _ hK
  obtain ⟨p, hp, hpA⟩ := exists_prime_val_lt h
  haveI : Fact p.Prime := ⟨hp⟩
  let W0 : Subgroup ↥(Ine (F := E) A) := (wildSub (E := E) A).comap (Ine (F := E) A).subtype
  haveI hW0 : W0.Normal := ⟨fun n hn g => conj_mem_wildSub (Ine_le_Dec A g.2) hn⟩
  let P : Subgroup (↥(Ine (F := E) A) ⧸ K) := W0.map (QuotientGroup.mk' K)
  haveI hPn : P.Normal := hW0.map _ (QuotientGroup.mk'_surjective K)
  have hpg : IsPGroup p P := by
    rintro ⟨_, s, hs, rfl⟩
    obtain ⟨O, hO, hOK⟩ := isOpen_induced_iff.mp hK
    have h1O : (1 : G E Ω) ∈ O := by
      have : (1 : ↥(Ine (F := E) A)) ∈ (Subtype.val ⁻¹' O) := by
        rw [hOK]; exact K.one_mem
      exact this
    obtain ⟨L, hL, hLO⟩ := (krullTopology_mem_nhds_one_iff E Ω O).mp (hO.mem_nhds h1O)
    obtain ⟨k, hk⟩ := Formalism.MainNotions.N.KillingConditions.WildPf.wildProP E Ω A p hp hpA (s : G E Ω) hs
      L.fixingSubgroup (IntermediateField.fixingSubgroup_isOpen L)
    refine ⟨k, Subtype.ext ?_⟩
    have hsk : s ^ (p ^ k) ∈ K := by
      have : s ^ (p ^ k) ∈ (Subtype.val ⁻¹' O : Set ↥(Ine (F := E) A)) := hLO (by simpa using hk)
      rw [hOK] at this
      exact this
    show (QuotientGroup.mk' K s) ^ (p ^ k) = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 hsk
  haveI : Group.IsNilpotent P := hpg.isNilpotent
  let c : ↥(Ine (F := E) A) →* ((↥(Ine (F := E) A) ⧸ K) ⧸ P) :=
    (QuotientGroup.mk' P).comp (QuotientGroup.mk' K)
  have hc1 : ∀ s ∈ K, c s = 1 := fun s hs => by
    have : QuotientGroup.mk' K s = 1 := (QuotientGroup.eq_one_iff _).2 hs
    show QuotientGroup.mk' P (QuotientGroup.mk' K s) = 1
    rw [this, map_one]
  have hc2 : ∀ s ∈ W0, c s = 1 := fun s hs =>
    (QuotientGroup.eq_one_iff _).2 ⟨s, hs, rfl⟩
  have hcs : Function.Surjective c :=
    (QuotientGroup.mk'_surjective P).comp (QuotientGroup.mk'_surjective K)
  obtain ⟨γ, hγI, hγ⟩ := GlobalTheory.TameInertiaGen.exists_tameGenAt E Ω w A h
  let γ' : ↥(Ine (F := E) A) := ⟨γ, hγI⟩
  let H : Subgroup ↥(Ine (F := E) A) := (Subgroup.zpowers (c γ')).comap c
  have hKH : K ≤ H := fun s hs => by
    have : c s ∈ Subgroup.zpowers (c γ') := by rw [hc1 s hs]; exact one_mem _
    exact this
  have hHc : IsClosed (H : Set ↥(Ine (F := E) A)) := H.isClosed_of_isOpen (Subgroup.isOpen_mono hKH hK)
  have hcl : IsClosed ((H.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) := by
    have := (isClosed_Ine (F := E) A).isClosedEmbedding_subtypeVal.isClosedMap _ hHc
    exact this
  have hle : Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) ≤
      H.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact ⟨γ', Subgroup.mem_zpowers _, rfl⟩
    · have hgI : g ∈ Ine (F := E) A := (GlobalTheory.InertiaTypePrimes.isWild_of_isWildAt A g hg).1
      have hcg : c ⟨g, hgI⟩ = 1 := hc2 _ hg
      have hin : c ⟨g, hgI⟩ ∈ Subgroup.zpowers (c γ') := by rw [hcg]; exact one_mem _
      exact ⟨⟨g, hgI⟩, hin, rfl⟩
  have hall : ∀ s : ↥(Ine (F := E) A), c s ∈ Subgroup.zpowers (c γ') := by
    intro s
    obtain ⟨t, ht, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hcl (hγ s.2)
    have : t = s := Subtype.ext e
    rw [← this]; exact ht
  have hcomm : ∀ a b : ((↥(Ine (F := E) A) ⧸ K) ⧸ P), a * b = b * a := by
    intro a b
    obtain ⟨s, rfl⟩ := hcs a
    obtain ⟨t, rfl⟩ := hcs b
    obtain ⟨m, hm⟩ := hall s
    obtain ⟨n, hn⟩ := hall t
    rw [← hm, ← hn]
    exact ((Commute.refl (c γ')).zpow_zpow m n).eq
  have hs2 : Group.IsSolvable ((↥(Ine (F := E) A) ⧸ K) ⧸ P) := isSolvable_of_comm hcomm
  have hs1 : Group.IsSolvable P := inferInstance
  have hker : (QuotientGroup.mk' P).ker ≤ P.subtype.range := fun x hx =>
    ⟨⟨x, (QuotientGroup.eq_one_iff _).1 hx⟩, rfl⟩
  exact solvable_of_ker_le_range P.subtype (QuotientGroup.mk' P) hker (hG' := hs1) (hG'' := hs2)

theorem exists_central_chain {Q : Type*} [Group Q] (hQ : Group.IsSolvable Q) (g : Q →* Multiplicative ℤ)
    (hf : Finite g.ker) (φ : Q) (hφ : g φ = Multiplicative.ofAdd 1) (P : Subgroup Q → Prop) (htop : P ⊤)
    (hstep : ∀ U V : Subgroup Q, P V → U ≤ V → ⁅V, V⁆ ≤ U → U.FiniteIndex → P U) :
    ∃ U : Subgroup Q, P U ∧ U.FiniteIndex ∧ ∀ x ∈ U, g x = 1 → x = 1 := by
  classical
  haveI := hf
  haveI : Finite (MulAut g.ker) :=
    Finite.of_injective (fun e : MulAut g.ker => (e.toEquiv : Equiv.Perm g.ker))
      (fun a b hab => MulEquiv.ext fun x => by
        have := congrArg (fun e : Equiv.Perm g.ker => e x) hab
        simpa using this)
  obtain ⟨f, hf0, hfc⟩ := (isOfFinOrder_of_finite (MulAut.conjNormal (H := g.ker) φ)).exists_pow_eq_one
  set z : Q := φ ^ f with hz
  have hzk : ∀ k ∈ g.ker, z * k = k * z := by
    intro k hk
    have h1 : MulAut.conjNormal (H := g.ker) z = 1 := by rw [hz, map_pow, hfc]
    have h2 := congrArg (fun e : MulAut g.ker => ((e ⟨k, hk⟩ : g.ker) : Q)) h1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc z * k = z * k * z⁻¹ * z := by group
      _ = k * z := by rw [h2]
  have hdec : ∀ x : Q, ∃ k ∈ g.ker, x = φ ^ (Multiplicative.toAdd (g x)) * k := by
    intro x
    refine ⟨(φ ^ (Multiplicative.toAdd (g x)))⁻¹ * x, ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hφ]
    apply Multiplicative.toAdd.injective
    simp
  have hzc : ∀ x : Q, z * x = x * z := by
    intro x
    obtain ⟨k, hk, e⟩ := hdec x
    have h1 : Commute z (φ ^ (Multiplicative.toAdd (g x))) := ((Commute.refl φ).pow_left f).zpow_right _
    have h2 : Commute z k := hzk k hk
    rw [e]
    exact (h1.mul_right h2).eq
  let Z : Subgroup Q := Subgroup.zpowers z
  have hZc : ∀ c ∈ Z, ∀ x : Q, c * x = x * c := by
    rintro c ⟨m, rfl⟩ x
    have : Commute z x := hzc x
    exact (this.zpow_left m).eq
  haveI hZn : Z.Normal := ⟨fun n hn x => by
    rw [← hZc n hn x, mul_inv_cancel_right]; exact hn⟩
  have hZfin : Z.FiniteIndex := by
    have hfpos : (0 : ℤ) < f := by exact_mod_cast Nat.pos_of_ne_zero hf0.ne'
    haveI : NeZero f := ⟨hf0.ne'⟩
    haveI : Finite (Q ⧸ Z) := by
      refine Finite.of_surjective
        (fun rk : Fin f × g.ker => (QuotientGroup.mk (φ ^ (rk.1 : ℕ) * (rk.2 : Q)) : Q ⧸ Z)) ?_
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨k, hk, e⟩ := hdec x
      set n : ℤ := Multiplicative.toAdd (g x) with hn
      have hr0 : 0 ≤ n % (f : ℤ) := Int.emod_nonneg _ hfpos.ne'
      have hrf : n % (f : ℤ) < f := Int.emod_lt_of_pos _ hfpos
      refine ⟨(⟨(n % (f : ℤ)).toNat, by omega⟩, ⟨k, hk⟩), ?_⟩
      show (QuotientGroup.mk (φ ^ (n % (f : ℤ)).toNat * k) : Q ⧸ Z) = QuotientGroup.mk x
      rw [QuotientGroup.eq]
      refine ⟨n / (f : ℤ), ?_⟩
      have e1 : (φ ^ (n % (f : ℤ)).toNat : Q) = φ ^ (n % (f : ℤ)) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hr0]
      have e2 : x = φ ^ (n % (f : ℤ)) * z ^ (n / (f : ℤ)) * k := by
        rw [e, hz, ← zpow_natCast, ← zpow_mul, ← zpow_add, Int.emod_add_mul_ediv]
      rw [e1]
      show z ^ (n / (f : ℤ)) = (φ ^ (n % (f : ℤ)) * k)⁻¹ * x
      have e3 : x = φ ^ (n % (f : ℤ)) * k * z ^ (n / (f : ℤ)) := by
        rw [e2, mul_assoc, mul_assoc, (hZc _ ⟨n / (f : ℤ), rfl⟩ k)]
      rw [e3]; group
    exact Subgroup.finiteIndex_of_finite_quotient
  have key : ∀ n : ℕ, P (derivedSeries Q n ⊔ Z) := by
    intro n
    induction n with
    | zero => simpa using htop
    | succ n ih =>
      refine hstep _ _ ih (sup_le_sup_right (derivedSeries_antitone Q (Nat.le_succ n)) _) ?_ ?_
      · rw [Subgroup.commutator_le]
        intro a ha b hb
        rw [← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at ha hb
        obtain ⟨a1, ha1, a2, ha2, rfl⟩ := ha
        obtain ⟨b1, hb1, b2, hb2, rfl⟩ := hb
        have c1 := hZc a2 ha2
        have c2 := hZc b2 hb2
        have h1 : a1 * a2 * (b1 * b2) = a1 * b1 * (a2 * b2) := by
          rw [mul_assoc a1 a2, ← mul_assoc a2 b1, c1 b1]; simp only [mul_assoc]
        have h2 : b1 * b2 * (a1 * a2) = b1 * a1 * (a2 * b2) := by
          rw [mul_assoc b1 b2, ← mul_assoc b2 a1, c2 a1, mul_assoc a1 b2, c2 a2]; simp only [mul_assoc]
        have e : a1 * a2 * (b1 * b2) * (a1 * a2)⁻¹ * (b1 * b2)⁻¹ = a1 * b1 * a1⁻¹ * b1⁻¹ := by
          have h3 : a1 * a2 * (b1 * b2) * (a1 * a2)⁻¹ * (b1 * b2)⁻¹ =
              (a1 * a2 * (b1 * b2)) * (b1 * b2 * (a1 * a2))⁻¹ := by group
          rw [h3, h1, h2]; group
        rw [commutatorElement_def, e]
        refine Subgroup.mem_sup_left ?_
        rw [derivedSeries_succ]
        exact Subgroup.commutator_mem_commutator ha1 hb1
      · exact Subgroup.finiteIndex_of_le (le_sup_right : Z ≤ _)
  obtain ⟨n, hn⟩ := hQ.solvable
  refine ⟨Z, ?_, hZfin, ?_⟩
  · have := key n
    rwa [hn, bot_sup_eq] at this
  · rintro x ⟨m, rfl⟩ hx
    have h1 : Multiplicative.toAdd (g (z ^ m)) = 0 := by rw [hx]; rfl
    rw [hz, map_zpow, map_pow, hφ] at h1
    have h2 : m * (f : ℤ) = 0 := by simpa using h1
    have hm : m = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd (by exact_mod_cast h) hf0.ne'
    simp [hm]

theorem exSub : ExSub := by
  intro E Ω _ _ _ _ _ A w h y
  induction y using WD.ind with
  | hP n a =>
  let K : Subgroup ↥(Weil h) := a.ρ.ker ⊓ (degHom h).ker
  haveI hKn : K.Normal := inferInstance
  let g : (↥(Weil h) ⧸ K) →* Multiplicative ℤ := QuotientGroup.lift K (degHom h) (fun x hx => hx.2)
  let K' : Subgroup ↥(Ine (F := E) A) := K.comap (ineIncl h)
  haveI hK'n : K'.Normal := inferInstance
  have hK'open : IsOpen (K' : Set ↥(Ine (F := E) A)) := by
    have : (K' : Set ↥(Ine (F := E) A)) = {σ | a.ρ (ineIncl h σ) = 1} := by
      ext σ
      constructor
      · intro hσ; exact hσ.1
      · intro hσ
        refine ⟨hσ, ?_⟩
        show degHom h (ineIncl h σ) = 1
        simp
    rw [this]
    exact a.smooth
  haveI := compactSpace_Ine (E := E) A
  haveI hfin : Finite (↥(Ine (F := E) A) ⧸ K') := Subgroup.quotient_finite_of_isOpen _ hK'open
  let f : (↥(Ine (F := E) A) ⧸ K') →* (↥(Weil h) ⧸ K) := QuotientGroup.map K' K (ineIncl h) le_rfl
  have hker : g.ker ≤ f.range := by
    intro x hx
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    have h0 : deg x = 0 := by
      have : degHom h x = 1 := hx
      simpa using this
    exact ⟨QuotientGroup.mk ⟨x, deg_eq_zero_iff.mp h0⟩, rfl⟩
  have hs1 := isSolvable_ine_quot h K' hK'open
  have hsol : Group.IsSolvable (↥(Weil h) ⧸ K) := solvable_of_ker_le_range f g hker (hG' := hs1)
  have hfk : Finite g.ker :=
    ((Set.finite_range f).subset (fun x hx => hker hx)).to_subtype
  have hci : ∀ U : Subgroup (↥(Weil h) ⧸ K), U.FiniteIndex → (U.comap (QuotientGroup.mk' K)).FiniteIndex :=
    fun U hU => ⟨by
      rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective K)]
      exact hU.index_ne_zero⟩
  obtain ⟨U, hU, hfi, hU1⟩ := exists_central_chain hsol g hfk (QuotientGroup.mk (frob h))
    (by show degHom h (frob h) = _; simp)
    (fun U => Sub (U.comap (QuotientGroup.mk' K)))
    (by simpa using Sub.top)
    (by
      intro U V hV hUV hc hfi
      haveI := hci U hfi
      refine Sub.step hV (Subgroup.comap_mono hUV) ?_ ?_ ?_
      · rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator]
        exact (Subgroup.commutator_mono (Subgroup.map_comap_le _ _) (Subgroup.map_comap_le _ _)).trans hc
      · exact (inferInstance : ((U.comap (QuotientGroup.mk' K)).subgroupOf
          (V.comap (QuotientGroup.mk' K))).FiniteIndex).index_ne_zero
      · have hle : K' ≤ (U.comap (QuotientGroup.mk' K)).comap (ineIncl h) := by
          intro x hx
          have : (QuotientGroup.mk' K) (ineIncl h x) = 1 := (QuotientGroup.eq_one_iff _).2 hx
          show (QuotientGroup.mk' K) (ineIncl h x) ∈ U
          rw [this]; exact U.one_mem
        exact Subgroup.isOpen_mono hle hK'open)
  haveI := hci U hfi
  refine ⟨U.comap (QuotientGroup.mk' K), hU, inferInstance, fun x hx hdeg => ?_⟩
  have h1 : (QuotientGroup.mk' K) x = 1 := hU1 _ hx (by
    show degHom h x = 1
    simp [hdeg])
  have h2 : x ∈ K := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : a.ρ x = 1 := h2.1
  simp only [Triv, WD.charPol_mk, WD.lpDim_mk, h3]
  simp [LinearMap.charpoly_one]

end GlobalTheory.CompanionTheory.ExSubLeaf
