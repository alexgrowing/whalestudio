import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem over_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A B : ValuationSubring Ω}
    (g : G F Ω) (hg : ∀ x, g x ∈ A ↔ x ∈ B) {w : HeightOneSpectrum (𝓞 F)} (hw : IsPlaceOver A w) :
    IsPlaceOver B w := by
  intro x
  rw [← hw x, valuation_lt_one_iff' (Ω := Ω), valuation_lt_one_iff' (Ω := Ω), ← hg, ← hg, map_inv₀, g.commutes]

private theorem not_dvd_index {Γ k : Type} [Group Γ] [Field k] [Finite k] {l : ℕ} [hl : Fact l.Prime] [CharP k l]
    (φ : Γ →* (Fin 4 → kˣ)) : ¬ l ∣ φ.ker.index := by
  rw [Subgroup.index_ker]
  intro h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' l (h.trans (Subgroup.card_subgroup_dvd_card _))
  have h1 : x = 1 := funext fun i => by
    have h2 : x i ^ l = 1 := by
      rw [← hx]
      exact congrFun (pow_orderOf_eq_one x) i
    have h3 : ((x i : k) - 1) ^ l = 0 := by
      rw [sub_pow_char, one_pow, ← Units.val_pow_eq_pow_val, h2, Units.val_one, sub_self]
    exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff hl.out.ne_zero |>.1 h3))
  rw [h1, orderOf_one] at hx
  exact hl.out.one_lt.ne hx

private theorem clos_eq {X : Type} [Group X] (s t : Set X) (h1 : ∀ x ∈ s, x = 1 ∨ x ∈ t) (h2 : t ⊆ s) :
    Subgroup.normalClosure t = Subgroup.normalClosure s := by
  refine le_antisymm (Subgroup.normalClosure_mono h2) (Subgroup.normalClosure_le_normal fun x hx => ?_)
  rcases h1 x hx with rfl | h
  · exact one_mem _
  · exact Subgroup.subset_normalClosure h

open scoped Pointwise in
theorem UpperTheory.V.Ws.X1.linkT :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∃ (S : Finset (HeightOneSpectrum (𝓞 T.F))) (K : Subgroup (G T.F Ω)) (Γ : Type) (_ : Group Γ) (_ : TopologicalSpace Γ) (_ : IsTopologicalGroup Γ) (_ : CompactSpace Γ) (_ : T2Space Γ) (_ : TotallyDisconnectedSpace Γ) (π : G T.F Ω →* Γ) (ι : T.ι ≃ S), GC.GLink l S K π ∧ (∀ w ∈ S, ((l : ℕ) : 𝓞 T.F) ∈ w.asIdeal) ∧ (∀ v, IsPlaceOver (T.pl v) (ι v).1) ∧ (T.fr ∅).Quo π := by
  intro Ω _ _ _ l hl c D T hT
  classical
  have hD : D.Good := hT.2.elim (fun h => h.1.1) fun h => h.1.1
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosure T.F Ω := ⟨inferInstance, inferInstance⟩
  haveI : IsGalois T.F Ω := {}
  obtain ⟨-, hfk, hlm, -⟩ := abelian₂.dvr_finite l c.O
  haveI := hfk
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact hlm)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hro, -⟩ := facts D hD
  have hcont : Continuous (resQ T.F) := (galEmbTop ℚ T.F Ω).1.continuous
  let K : Subgroup (G T.F Ω) := D.rbar.ker.comap (resQ T.F)
  have hKo : IsOpen (K : Set (G T.F Ω)) := hro.preimage hcont
  have hKi : ¬ l ∣ K.index := by
    have h1 : K = (MonoidHom.pi fun i =>
        ((Units.map (residue c.O).toMonoidHom).comp (D.ps i)).comp (resQ T.F)).ker := by
      ext g
      show D.rbar (resQ T.F g) = 1 ↔ _
      rw [MonoidHom.mem_ker]
      refine ⟨fun h => funext fun i => Units.ext ?_, fun h => ?_⟩
      · simpa [Raw.rbar, Raw.r0, diagRep, mapRep] using congrFun (congrFun h i) i
      · ext i j
        by_cases e : i = j
        · subst e
          simpa [Raw.rbar, Raw.r0, diagRep, mapRep] using congrArg Units.val (congrFun h i)
        · simp [Raw.rbar, Raw.r0, diagRep, mapRep, e]
    rw [h1]
    exact not_dvd_index _
  have hfin : {v : HeightOneSpectrum (𝓞 T.F) | ((l : ℕ) : 𝓞 T.F) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((l : ℕ) : 𝓞 T.F)})
      (mt Ideal.span_singleton_eq_bot.1 (Nat.cast_ne_zero.2 hl.out.ne_zero))).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  let S := hfin.toFinset
  have hS : ∀ v, v ∈ S ↔ ((l : ℕ) : 𝓞 T.F) ∈ v.asIdeal := fun v => hfin.mem_toFinset
  have hval : ∀ {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 T.F)}, IsPlaceOver A v →
      (A.valuation (l : Ω) < 1 ↔ ((l : ℕ) : 𝓞 T.F) ∈ v.asIdeal) := fun {A v} h => (places T.F Ω l A).2.2.1 v h
  let N := GC.tameN (S : Set (HeightOneSpectrum (𝓞 T.F))) K
  haveI : N.Normal := Subgroup.is_normal_topologicalClosure _
  haveI hNc : IsClosed (N : Set (G T.F Ω)) := Subgroup.isClosed_topologicalClosure _
  have h0 : ∀ u : T.ι, ∃ w : S, IsPlaceOver (T.pl u) w.1 := fun u => by
    obtain ⟨a1, a2, -⟩ := places T.F Ω l (T.pl u)
    obtain ⟨w, hw⟩ := a1 fun h => (a2 h).2 (T.ovl u)
    exact ⟨⟨w, (hS w).2 ((hval hw).1 (T.ovl u))⟩, hw⟩
  choose pl hp using h0
  have hbij : Function.Bijective pl := by
    refine ⟨fun a b h => ?_, fun w => ?_⟩
    · obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := T.F) (hp a) (h ▸ hp b)
      refine (T.cover (T.pl b) (T.ovl b)).unique ⟨g, fun x => ?_⟩ ⟨1, fun _ => Iff.rfl⟩
      show g • x ∈ T.pl b ↔ _
      rw [← hg]
      exact ValuationSubring.smul_mem_pointwise_smul_iff
    · obtain ⟨A, hA⟩ : ∃ A : ValuationSubring Ω, IsPlaceOver A w.1 := exists_isPlaceOver Ω w.1
      obtain ⟨u, ⟨g, hg⟩, -⟩ := T.cover A ((hval hA).2 ((hS _).1 w.2))
      exact ⟨u, Subtype.ext (eq_of_isPlaceOver (hp u) (over_move g hg hA))⟩
  refine ⟨S, K, G T.F Ω ⧸ N, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (AlgebraTools.totallyDisconnected_quot _ N hNc).1, QuotientGroup.mk' N, Equiv.ofBijective pl hbij,
    GC.gLink_quot l hD.l_odd (fun v hv => (hS v).2 hv) inferInstance hKo hKi, fun w hw => (hS w).1 hw, hp,
    QuotientGroup.continuous_mk, QuotientGroup.mk'_surjective _, ?_⟩
  rw [QuotientGroup.ker_mk']
  refine congrArg Subgroup.topologicalClosure (clos_eq _ _ ?_ fun x hx => ?_)
  · rintro x ⟨A, hA, h1, h2⟩
    obtain ⟨a1, a2, -⟩ := places T.F Ω l A
    by_cases ht : A = ⊤
    · rw [(a2 ht).1, Subgroup.mem_bot] at h1
      exact Or.inl h1
    · obtain ⟨v, hv⟩ := a1 ht
      refine Or.inr ?_
      simp only [Set.mem_iUnion]
      exact ⟨v, fun h => hA l (Finset.mem_insert_self _ _) ((hval hv).2 ((hS v).1 h)), A, hv, h1, h2⟩
  · simp only [Set.mem_iUnion] at hx
    obtain ⟨v, hv, A, hA, h1, h2⟩ := hx
    refine ⟨A, fun p hp h => ?_, h1, h2⟩
    obtain rfl : p = l := by simpa using hp
    exact hv ((hS v).2 ((hval hA).1 h))
