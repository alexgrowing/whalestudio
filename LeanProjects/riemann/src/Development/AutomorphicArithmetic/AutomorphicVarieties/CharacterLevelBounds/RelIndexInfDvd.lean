import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ShaFamMono
import Development.AutomorphicArithmetic.AutomorphicVarieties.PartsSign
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.KerFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.KerIdx
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.H0LocalCardBoundedOfClsKerLeKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.PlacesQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CokerAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Chr

private theorem relIndex_inf_dvd {G : Type} [Group G] (U' U D : Subgroup G) [U'.Normal] :
    (U' ⊓ D).relIndex (U ⊓ D) ∣ U'.relIndex U := by
  have e : (U' ⊓ D).relIndex (U ⊓ D) = U'.relIndex (U ⊓ D) := by
    unfold Subgroup.relIndex
    congr 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2.2⟩⟩
  rw [e]
  have k : ∀ K : Subgroup G, U'.relIndex K = Nat.card (K.map (QuotientGroup.mk' U')) := fun K => by
    rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']
  rw [k, k]
  exact Subgroup.card_dvd_of_le (Subgroup.map_mono inf_le_left)

private theorem comm_inf {G : Type} [Group G] (U' D : Subgroup G) (h : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ U') :
    ∀ a ∈ ⊤ ⊓ D, ∀ b ∈ ⊤ ⊓ D, a * b * a⁻¹ * b⁻¹ ∈ U' ⊓ D := fun a ha b hb =>
  ⟨h a b, D.mul_mem (D.mul_mem (D.mul_mem ha.2 hb.2) (D.inv_mem ha.2)) (D.inv_mem hb.2)⟩

theorem UpperTheory.V.Chr.eigLe :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (N : ℕ) [NeZero N] (H : Subgroup (ZMod N)ˣ) (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] (e : ℕ) (ψ : G ℚ Ω →* Oˣ), e ≠ 0 → levH ℚ Ω H ≤ ψ.ker →
          eigL l e (levH ℚ Ω H) ψ ≤ V l e ψ + (loss l N H.index e : ℕ∞) * eO l O := by
  intro Ω _ _ _ N _ H l hl O _ _ _ _ _ e ψ he hψ
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  obtain ⟨hopen, -, -, -, hine⟩ := clsFacts ℚ Ω N
  obtain ⟨hex, hN, hconj⟩ := placesQ Ω
  have hk : (cls ℚ Ω N).ker ≤ levH ℚ Ω H := fun g hg => by
    show cls ℚ Ω N g ∈ H
    rw [MonoidHom.mem_ker.1 hg]
    exact H.one_mem
  have hUo : IsOpen (levH ℚ Ω H : Set (G ℚ Ω)) := Subgroup.isOpen_mono hk hopen
  have hψi : levH ℚ Ω H ≤ (ψ⁻¹).ker := fun g hg => by
    rw [MonoidHom.mem_ker, MonoidHom.inv_apply, MonoidHom.mem_ker.1 (hψ hg), inv_one]
  have hc : ContAction (rho l e ψ) := (contTw ℚ Ω l).2.2 O ψ⁻¹ _ (Subgroup.isOpen_mono hψi hUo)
  have hcomm : ∀ a b : G ℚ Ω, a * b * a⁻¹ * b⁻¹ ∈ levH ℚ Ω H := fun a b => by
    show cls ℚ Ω N _ ∈ H
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_cancel_comm, mul_inv_cancel]
    exact H.one_mem
  have hn : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hdvd : (levH ℚ Ω H).relIndex ⊤ ∣ H.index := by
    rw [Subgroup.relIndex_top_right, levH, Subgroup.index_comap]
    exact Subgroup.relIndex_dvd_index_of_normal _ _
  obtain ⟨hb1, hb2⟩ := H0_local_card_bounded_of_cls_ker_le_ker Ω l O N e ψ he (hk.trans hψ)
  obtain ⟨A₀, hA₀⟩ := hex l hl.out
  have hA : ∀ p : N.primeFactors, ∃ A : ValuationSubring Ω, ¬ A.valuation (l : Ω) < 1 ∧
      ∀ A' : ValuationSubring Ω, A'.valuation ((p : ℕ) : Ω) < 1 → ¬ A'.valuation (l : Ω) < 1 →
        ∃ u : G ℚ Ω, ∀ x ∈ Ine (F := ℚ) A', u⁻¹ * x * u ∈ Ine (F := ℚ) A := by
    intro p
    by_cases h : ∃ A : ValuationSubring Ω, A.valuation ((p : ℕ) : Ω) < 1 ∧ ¬ A.valuation (l : Ω) < 1
    · obtain ⟨A, h1, h2⟩ := h
      exact ⟨A, h2, fun A' h3 _ =>
        (hconj p A' A (Nat.prime_of_mem_primeFactors p.2) h3 h1).imp fun _ hu => hu.2⟩
    · exact ⟨⊤, ((places ℚ Ω l ⊤).2.1 rfl).2, fun A' h3 h4 => absurd ⟨A', h3, h4⟩ h⟩
  choose A hAl hAc using hA
  have hID : ∀ B : ValuationSubring Ω, Ine (F := ℚ) B ≤ Dec (F := ℚ) B := fun _ _ h => h.1
  let D : Option N.primeFactors → Subgroup (G ℚ Ω) := fun i => i.elim (Dec (F := ℚ) A₀) fun p => Ine (F := ℚ) (A p)
  have h1 := selDown O _ _ (rho l e ψ) (levH ℚ Ω H) ⊤ le_top _ (conjStable_shaFam ℚ Ω l) _ D
    (by
      rintro (_ | p)
      · exact Or.inl ⟨A₀, hA₀, rfl⟩
      · exact Or.inr ⟨A p, rfl⟩)
    (by
      have hd : ∀ B : ValuationSubring Ω, B.valuation (l : Ω) < 1 →
          ∃ u : G ℚ Ω, ∀ x ∈ Dec (F := ℚ) B, u⁻¹ * x * u ∈ D none := fun B hB =>
        (hconj l B A₀ hl.out hB hA₀).imp fun _ hu => hu.1
      rintro _ (⟨B, hB, rfl⟩ | ⟨B, rfl⟩)
      · obtain ⟨u, hu⟩ := hd B hB
        exact Or.inr ⟨none, u, trivial, fun x hx => hu x hx.2⟩
      · by_cases hB : B.valuation (l : Ω) < 1
        · obtain ⟨u, hu⟩ := hd B hB
          exact Or.inr ⟨none, u, trivial, fun x hx => hu x (hID B hx.2)⟩
        · by_cases hB' : B.valuation (N : Ω) < 1
          · obtain ⟨p, hp, hp'⟩ := (hN B N (NeZero.ne N)).1 hB'
            obtain ⟨u, hu⟩ := hAc ⟨p, hp⟩ B hp' hB
            exact Or.inr ⟨some ⟨p, hp⟩, u, trivial, fun x hx => hu x hx.2⟩
          · exact Or.inl (inf_le_right.trans ((hine B hB').trans hk)))
  have h2 := (selTwist O _ _ (twist₂ l (chiO ℚ Ω l O ^ (-(e : ℤ)))) (rho l e ψ) ψ (tw_apply l e ψ) (levH ℚ Ω H)
    (fun u hu => hψ hu) _ (conjStable_shaFam ℚ Ω l)).2 ⊤ 1
  rw [mul_one] at h2
  have h3 := cokerAb O _ _ (rho l e ψ) hc (qoFacts l O).1 (fun g => ⟨_, fun _ => rfl⟩) (levH ℚ Ω H) ⊤ le_top
    isClosed_univ (hUo.preimage continuous_subtype_val) fun a _ b _ => hcomm a b
  have h3' := h3.trans (mul_le_mul' (pow_le_pow_left' (Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd)) 2) hb2)
  have h4 := (kerIdx l O _ _ hc _ _ (inf_le_inf_right (D none) (le_top : levH ℚ Ω H ≤ ⊤)) (comm_inf _ _ hcomm) _ hn
    ((relIndex_inf_dvd _ _ _).trans hdvd)).trans (mul_le_mul' le_rfl (hb1 A₀ _ hA₀ (le_inf le_top (hID A₀))))
  have h5 : ∀ p : N.primeFactors, _ := fun p =>
    kerFin l O _ _ hc _ _ (inf_le_inf_right (D (some p)) (le_top : levH ℚ Ω H ≤ ⊤)) (fun g hg => by
      have e1 : chiO ℚ Ω l O g = 1 := by
        have := MonoidHom.mem_ker.1 ((places ℚ Ω l (A p)).2.2.2 (hAl p) hg.2)
        rw [chiO, MonoidHom.comp_apply, this, map_one]
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.mem_ker.1 (hψi hg.1), one_mul]
      show chiO ℚ Ω l O g ^ (-(e : ℤ)) = 1
      rw [e1, one_zpow]) (comm_inf _ _ hcomm) _ hn ((relIndex_inf_dvd _ _ _).trans hdvd)
  rw [Fintype.sum_option] at h1
  have h6 := (Finset.sum_le_sum fun p (_ : p ∈ Finset.univ) => h5 p).trans_eq (Finset.sum_const _)
  refine (h2.le.trans (h1.trans (add_le_add (add_le_add le_rfl (add_le_add h4 h6)) h3'))).trans_eq ?_
  rw [Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, loss, add_assoc]
  congr 1
  push_cast
  ring
