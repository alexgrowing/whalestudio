import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TrdegQuotLeOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocFlat
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.KrullDimQuotientBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem char_triv {l : ℕ} [hl : Fact l.Prime] {D : Type} [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [CharP D l] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G] (ψ : G →* D)
    (hc : AdicCont (maximalIdeal D) ψ) (q : ℕ) (hq : q.Coprime l) (h1 : ∀ g, ψ g ^ q - 1 ∈ maximalIdeal D)
    {ι : Type} (u : ι → G) (hu : ∀ a, ψ (u a) = 1) (g : G) (hg : ψ g - 1 ∈ maximalIdeal D)
    (H : ∀ (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : G →* A, IsOpen (χ.ker : Set G) →
      (∀ a, χ (u a) = 1) → χ g = 1) : ψ g = 1 := by
  have hm := (maximalIdeal D)
  have key : ∀ N : ℕ, ψ g - 1 ∈ (maximalIdeal D) ^ N := by
    intro N
    set I := (maximalIdeal D) ^ N with hIdef
    let f : G →* (D ⧸ I)ˣ :=
      (powMonoidHom q).comp ((Units.map (Ideal.Quotient.mk I : D →+* D ⧸ I).toMonoidHom).comp ψ.toHomUnits)
    have hfv : ∀ x, ((f x : (D ⧸ I)ˣ) : D ⧸ I) = Ideal.Quotient.mk I (ψ x ^ q) := by
      intro x
      simp [f]
    have hlc : IsLocallyConstant (fun x => ((f x : (D ⧸ I)ˣ) : D ⧸ I)) := by
      have h0 : IsLocallyConstant (fun x => (Ideal.Quotient.mk I (ψ x)) ^ q) :=
        (hc N).comp (fun y => y ^ q)
      convert h0 using 1
      funext x
      rw [hfv, map_pow]
    have hlcf : IsLocallyConstant f := IsLocallyConstant.desc _ _ hlc Units.val_injective
    have hfin : Finite f.range := by
      have h := hlcf.range_finite
      rw [← MonoidHom.coe_range] at h
      exact h.to_subtype
    have hmem : ∀ x : D, x - 1 ∈ maximalIdeal D → Ideal.Quotient.mk I (x ^ (l ^ N)) = 1 := by
      intro x hx
      rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
      have hch : (x - 1) ^ (l ^ N) = x ^ (l ^ N) - 1 := by
        rw [sub_pow_char_pow, one_pow]
      rw [← hch]
      exact Ideal.pow_le_pow_right (Nat.lt_pow_self hl.out.one_lt).le (Ideal.pow_mem_pow hx _)
    have hP : IsPGroup l f.range := by
      rintro ⟨x, ⟨y, rfl⟩⟩
      refine ⟨N, ?_⟩
      apply Subtype.ext
      apply Units.ext
      simp only [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one, Units.val_one]
      rw [hfv, ← map_pow]
      exact hmem _ (h1 y)
    have hopen : IsOpen (f.rangeRestrict.ker : Set G) := by
      rw [MonoidHom.ker_rangeRestrict]
      exact hlcf.isOpen_fiber 1
    have hχ := H f.range hP f.rangeRestrict hopen (fun a => by
      apply Subtype.ext
      apply Units.ext
      simp only [MonoidHom.coe_rangeRestrict, OneMemClass.coe_one, Units.val_one]
      rw [hfv, hu, one_pow, map_one])
    have hq1 : Ideal.Quotient.mk I (ψ g) ^ q = 1 := by
      have h2 := congrArg (fun z : f.range => ((z : (D ⧸ I)ˣ) : D ⧸ I)) hχ
      simp only [MonoidHom.coe_rangeRestrict, OneMemClass.coe_one, Units.val_one] at h2
      rw [hfv, map_pow] at h2
      exact h2
    have hl1 : Ideal.Quotient.mk I (ψ g) ^ (l ^ N) = 1 := by
      rw [← map_pow]
      exact hmem _ hg
    have hgcd := pow_gcd_eq_one.2 ⟨hq1, hl1⟩
    rw [Nat.Coprime.pow_right N hq, pow_one, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at hgcd
    exact hgcd
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal D) (maximalIdeal.isMaximal D).ne_top
  have hmem : ψ g - 1 ∈ ⨅ i, (maximalIdeal D) ^ i := Ideal.mem_iInf.2 key
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at hmem
  exact hmem

section

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsCoef l O] {F : UpperTheory.V.Fr.Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}

private theorem psi_pow (S : Space O F n) (v : F.V) (i : Fin n) (g : F.Gv v) (q : ℕ)
    (h : F.Ψ (F.loc v g) ^ q = 1) : S.ψB v i g ^ q - 1 ∈ S.mB := by
  obtain ⟨-, hbar, -⟩ := S.lift
  have h2 := hbar.2 v i g
  simp only [NRep.map, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe,
    RingHom.id_apply] at h2
  show ((S.ψB v i g ^ q - 1 : S.B) : S.R) ∈ maximalIdeal S.R
  rw [← res_eq_zero_iff O S.R]
  simp only [Subalgebra.coe_sub, Subalgebra.coe_pow, Subalgebra.coe_one, map_sub, map_pow, map_one]
  change (res O S.R) (S.ρ.ψ v i g : S.R) ^ q - 1 = 0
  have h3 : (res O S.R) (S.ρ.ψ v i g : S.R) = ((F.Ψ (F.loc v g) ^ w n i : (ResidueField O)ˣ) : ResidueField O) := h2
  rw [h3, ← Units.val_pow_eq_pow_val, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, h,
    _root_.one_zpow, Units.val_one, sub_self]

private theorem space_psiB_apply_one (S : Space O F n) (v : F.V) (i : Fin n) : S.ψB v i 1 = 1 := by
  apply Subtype.ext
  simp [Space.ψB]

private theorem space_psiB_apply_mul (S : Space O F n) (v : F.V) (i : Fin n) (g h : F.Gv v) :
    S.ψB v i (g * h) = S.ψB v i g * S.ψB v i h := by
  apply Subtype.ext
  simp [Space.ψB]

private theorem natCard_units_residueField_coprime : (Nat.card (ResidueField O)ˣ).Coprime l := by
  classical
  have hl : l.Prime := Fact.out
  letI : Fintype (ResidueField O) := Fintype.ofFinite _
  obtain ⟨m, -, hm⟩ := FiniteField.card (ResidueField O) l
  rw [Nat.card_eq_fintype_card, Fintype.card_units, hm]
  apply Nat.Coprime.symm
  rw [Nat.Prime.coprime_iff_not_dvd hl]
  intro hd
  have hpos : 0 < l ^ (m : ℕ) := pow_pos hl.pos _
  have h2 : l ∣ l ^ (m : ℕ) := dvd_pow_self l (PNat.ne_zero m)
  have h3 : l ∣ l ^ (m : ℕ) - (l ^ (m : ℕ) - 1) := Nat.dvd_sub h2 hd
  rw [Nat.sub_sub_self hpos] at h3
  exact hl.one_lt.ne' (Nat.dvd_one.1 h3)

private theorem lam_le (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (S : Space O F n) (u : ∀ v, Fin (F.dv v) → F.Gv v)
    (H : ∀ v (A : Type) [CommGroup A] [Finite A], IsPGroup l A → ∀ χ : F.Gv v →* A,
      IsOpen (χ.ker : Set (F.Gv v)) → (∀ a, χ (u v a) = 1) → ∀ g ∈ F.Iv v, χ g = 1)
    (Q : Ideal S.B) (hQ : Q.IsPrime) (hO : (maximalIdeal O).map (algebraMap O S.B) ≤ Q)
    (hu : ∀ v i a, S.ψB v i (u v a) - 1 ∈ Q) : S.lamId ≤ Q := by
  classical
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  haveI := hco
  haveI : Q.IsPrime := hQ
  haveI : Nontrivial (S.B ⧸ Q) := Ideal.Quotient.nontrivial_iff.mpr hQ.ne_top
  haveI : IsLocalRing (S.B ⧸ Q) := IsLocalRing.of_surjective' (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk Q) :=
    Function.Surjective.isLocalHom (Ideal.Quotient.mk Q) Ideal.Quotient.mk_surjective
  let f0 : ResidueField O →+* S.B ⧸ Q :=
    Ideal.Quotient.lift (maximalIdeal O) ((Ideal.Quotient.mk Q).comp (algebraMap O S.B)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hO (Ideal.mem_map_of_mem _ ha))
  haveI : CharP (S.B ⧸ Q) l := charP_of_injective_ringHom f0.injective l
  have hmapm : ∀ x ∈ S.mB, Ideal.Quotient.mk Q x ∈ maximalIdeal (S.B ⧸ Q) := by
    intro x hx
    rw [← hmax] at hx
    exact (IsLocalRing.mem_maximalIdeal _).2 fun hu => (IsLocalRing.mem_maximalIdeal x).1 hx (isUnit_of_map_unit _ x hu)
  apply sup_le hO
  rw [Ideal.span_le]
  rintro x ⟨v, i, g, hgI, hgΨ, rfl⟩
  let ψQ : F.Gv v →* S.B ⧸ Q :=
    { toFun := fun g => Ideal.Quotient.mk Q (S.ψB v i g)
      map_one' := by simp [space_psiB_apply_one]
      map_mul' := fun a b => by simp [space_psiB_apply_mul] }
  have hcont : AdicCont (maximalIdeal (S.B ⧸ Q)) ψQ := by
    intro N
    have hN := (cont_u hF hn S).2.2.1 v i N
    have hle : ∀ a ∈ S.mB ^ N, ((Ideal.Quotient.mk (maximalIdeal (S.B ⧸ Q) ^ N)).comp (Ideal.Quotient.mk Q)) a = 0 := by
      intro a ha
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      have : Ideal.map (Ideal.Quotient.mk Q) (S.mB ^ N) ≤ maximalIdeal (S.B ⧸ Q) ^ N := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hmapm) N
      exact this (Ideal.mem_map_of_mem _ ha)
    have h2 := hN.comp (Ideal.Quotient.lift (S.mB ^ N) _ hle)
    convert h2 using 1
    funext g
    simp only [Function.comp_apply, Ideal.Quotient.lift_mk, RingHom.comp_apply]
    rfl
  have key := char_triv ψQ hcont (Nat.card (ResidueField O)ˣ) natCard_units_residueField_coprime
    (fun g => by
      have := psi_pow S v i g _ (pow_card_eq_one')
      have h2 := hmapm _ this
      simpa [ψQ] using h2)
    (u v) (fun a => by
      show Ideal.Quotient.mk Q (S.ψB v i (u v a)) = 1
      rw [← map_one (Ideal.Quotient.mk Q), Ideal.Quotient.eq]
      exact hu v i a) g
    (by
      have := psi_pow S v i g 1 (by rw [pow_one, hgΨ])
      have h2 := hmapm _ this
      simpa [ψQ] using h2)
    (fun A _ _ hA χ ho hχ => H v A hA χ ho hχ g hgI)
  show S.ψB v i g - 1 ∈ Q
  rw [← Ideal.Quotient.eq, map_one]
  exact key

private theorem dim_B (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) (S : Space O F n) (I : Ideal S.B) (hI : S.FinLam I)
    (v : F.V) (i j : Fin n) (hij : i ≠ j) (p : Ideal S.B) (hp : I ≤ p)
    (hc : ∀ g ∈ F.Nv v, S.ψB v i g - S.ψB v j g ∈ p) :
    ∃ m : ℕ, ringKrullDim (S.B ⧸ p) ≤ m ∧ m + F.dv v ≤ n * F.d + 2 := by
  classical
  obtain ⟨hco, hmax⟩ := co_B hF hn S
  haveI := hco
  choose u a₀ hu1 hu2 hgen using hF.gen
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let ι := Unit ⊕ Unit ⊕ {x : Σ w, Fin n × Fin (F.dv w) // ¬(x.1 = v ∧ x.2.1 = j)}
  let t : ι → S.B := fun z => match z with
    | Sum.inl _ => algebraMap O S.B ϖ
    | Sum.inr (Sum.inl _) => S.ψB v j (u v (a₀ v)) - 1
    | Sum.inr (Sum.inr x) => S.ψB x.1.1 x.1.2.1 (u x.1.1 x.1.2.2) - 1
  have hψm : ∀ w i' a, S.ψB w i' (u w a) - 1 ∈ maximalIdeal S.B := by
    intro w i' a
    rw [hmax]
    have := psi_pow S w i' (u w a) 1 (by rw [pow_one]; exact (hu1 w a).2)
    rwa [pow_one] at this
  have ht : ∀ z, t z ∈ maximalIdeal S.B := by
    rintro (_ | _ | x)
    · exact map_nonunit (algebraMap O S.B) ϖ ((IsLocalRing.mem_maximalIdeal ϖ).2 hϖ.not_isUnit)
    · exact hψm _ _ _
    · exact hψm _ _ _
  have hcut := krull_dim_quotient_bound p (maximalIdeal S.B) t ht (by
    intro P hP hpP htP
    have hO : (maximalIdeal O).map (algebraMap O S.B) ≤ P := by
      rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      exact htP (Sum.inl ())
    have hu : ∀ w i' a, S.ψB w i' (u w a) - 1 ∈ P := by
      intro w i' a
      by_cases hx : w = v ∧ i' = j
      · obtain ⟨rfl, rfl⟩ := hx
        by_cases ha : a = a₀ w
        · subst ha
          exact htP (Sum.inr (Sum.inl ()))
        · have h1 : S.ψB w i (u w a) - 1 ∈ P := htP (Sum.inr (Sum.inr ⟨⟨w, i, a⟩, fun h => hij h.2⟩))
          have h2 : S.ψB w i (u w a) - S.ψB w i' (u w a) ∈ P := hpP (hc _ (hu2 w a ha))
          have := P.sub_mem h1 h2
          rwa [sub_sub_sub_cancel_left] at this
      · exact htP (Sum.inr (Sum.inr ⟨⟨w, i', a⟩, hx⟩))
    have hlam := lam_le hF hn S u hgen P hP hO hu
    rw [hmax]
    calc S.mB ≤ (I ⊔ S.lamId).radical := hI
      _ ≤ P.radical := Ideal.radical_mono (sup_le (hp.trans hpP) hlam)
      _ = P := hP.radical)
  have hfield : ringKrullDim (S.B ⧸ maximalIdeal S.B) = 0 :=
    ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 (maximalIdeal.isMaximal _))
  rw [hfield, zero_add] at hcut
  refine ⟨Fintype.card ι, hcut, ?_⟩
  let e : ι ⊕ Fin (F.dv v) → Unit ⊕ Unit ⊕ (Σ w, Fin n × Fin (F.dv w)) := fun z => match z with
    | Sum.inl (Sum.inl _) => Sum.inl ()
    | Sum.inl (Sum.inr (Sum.inl _)) => Sum.inr (Sum.inl ())
    | Sum.inl (Sum.inr (Sum.inr x)) => Sum.inr (Sum.inr x.1)
    | Sum.inr a => Sum.inr (Sum.inr ⟨v, j, a⟩)
  have he : Function.Injective e := by
    rintro ((_ | _ | x) | a) ((_ | _ | y) | b) h <;> simp only [e, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at h
    · rfl
    · rfl
    · rw [Subtype.ext h]
    · exact absurd ⟨congrArg Sigma.fst h, congrArg (fun s : (Σ w, Fin n × Fin (F.dv w)) => s.2.1) h⟩ x.2
    · exact absurd ⟨(congrArg Sigma.fst h).symm, (congrArg (fun s : (Σ w, Fin n × Fin (F.dv w)) => s.2.1) h).symm⟩ y.2
    · rw [Sigma.mk.inj_iff] at h
      have := h.2
      simp at this
      rw [this]
  have hc2 := Fintype.card_le_of_injective e he
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin] at hc2
  rw [← Finset.mul_sum] at hc2
  unfold Frame.d
  omega

end

theorem UpperTheory.V.Fr.l52 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ∀ I : Ideal S.B, S.FinLam I → ∀ v i j, i ≠ j → ∀ P : Ideal L.R, P.IsPrime → L.ρ.OffTri P → I ≤ L.π P → L.ρ.Coin P v i j → ringKrullDim (L.R ⧸ P) + F.dv v ≤ (n * F.d + 6 : ℕ) ∧ ((maximalIdeal O).map (algebraMap O L.R) ≤ P → ringKrullDim (L.R ⧸ P) + F.dv v ≤ (n * F.d + 5 : ℕ)) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L I hI v i j hij P hP hoff hIP hcoin
  haveI := hP
  have hrho := loc_rho hF hn S x L
  have hiff := hrho.2.2.1 P
  have hη : (L.im P).IsPrime := Ideal.comap_isPrime _ P
  have hoffS : S.u.OffTri (L.im P) := ⟨fun h => hoff.1 (hiff.1.2 h), fun h => hoff.2 (hiff.2.1.2 h)⟩
  have hfib := fibre hF hn S (L.im P) hη hoffS
  have hdim := (loc_dim hF hn S x L).1 P hP 1 (by simpa using hfib)
  have hc : ∀ g ∈ F.Nv v, S.ψB v i g - S.ψB v j g ∈ L.π P := by
    intro g hg
    have h := hcoin g hg
    show L.ι (S.inc (S.ψB v i g - S.ψB v j g)) ∈ P
    rw [map_sub, map_sub]
    exact h
  obtain ⟨m, hm1, hm2⟩ := dim_B hF hn S I hI v i j hij (L.π P) hIP hc
  have key : ringKrullDim (L.R ⧸ P) + F.dv v ≤ ((m + 1 + F.dv v : ℕ) : WithBot ℕ∞) := by
    calc ringKrullDim (L.R ⧸ P) + F.dv v ≤ ((m : WithBot ℕ∞) + ((1 : ℕ) : WithBot ℕ∞)) + F.dv v :=
          add_le_add (hdim.trans (add_le_add hm1 le_rfl)) le_rfl
      _ = ((m + 1 + F.dv v : ℕ) : WithBot ℕ∞) := by push_cast; rfl
  refine ⟨key.trans ?_, fun _ => key.trans ?_⟩
  · exact_mod_cast (by omega)
  · exact_mod_cast (by omega)
