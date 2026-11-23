import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.MemMaxIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.TwistMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.TwistPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.TwistFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.NoCompl
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.AdjointBlockSubmatrixEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem not_over {Ω : Type} [Field Ω] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (e : q ≠ p) {A : ValuationSubring Ω}
    (hA : A.valuation (p : Ω) < 1) : ¬ A.valuation (q : Ω) < 1 := fun hq' => by
  obtain ⟨a, b, hab⟩ : IsCoprime (q : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hp).2 e)
  have h1 : A.valuation ((a : Ω) * (q : Ω) + (b : Ω) * (p : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hq'
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A b))) hA
  have h2 : (a : Ω) * (q : Ω) + (b : Ω) * (p : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

section
variable {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R')

private theorem uM_map {Y : M4 R} (h : Y ∈ uM R) : Y.map f ∈ uM R' := by
  refine ⟨fun i j e => by rw [Matrix.map_apply, h.1 i j e, map_zero], ?_⟩
  have e : adj Y = -Y := h.2
  show adj _ = -_
  rw [(grp R).2.2.2.2.2.1, e]
  ext i j
  simp

private theorem blk_map {Y : M4 R} (h : IsBlock Y) : IsBlock (Y.map f) := fun i j e => by
  rw [Matrix.map_apply, h i j e, map_zero]

private theorem rep_eq {Γ : Type} [Group Γ] (r : Γ →* M4 R) (g : Γ) : mapRep f r g = f.mapMatrix (r g) := rfl

private theorem adj_map (Y : M4 R) : adj (f.mapMatrix Y) = f.mapMatrix (adj Y) := (grp R).2.2.2.2.2.1 R' f Y

private theorem eAB_map : (eAB R).map f = eAB R' := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eAB]

end

theorem UpperTheory.V.Ws.bl :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (𝔞 : Amb l) r u, KPair D 𝔞 r u → (∀ g, IsBlock (r g)) →
      Submodule.span 𝔞.K (Set.range fun g => (mapRep 𝔞.toK r g).submatrix ixA ixA) = ⊤ →
      ∃ r' u', KPair D 𝔞 r' u' ∧ BlockExt (mapRep 𝔞.toK r') ∧ ∀ g, (r' g).charpoly = (r g).charpoly := by
  intro hP Ω _ _ _ l hl c D hD 𝔞 r u hK hB hsp
  obtain ⟨hpos, h2, A, _, _, _, f, r₁, u₁, hf, hr, hu, hlA, hb⟩ := toGlobalTheory D hD 𝔞 r u hK hB
  haveI := hf.fin
  haveI := hf.loc
  obtain ⟨r', z, y, e, hc, hz, hy, hm, hzc, hN, hfl, hne⟩ := cocA hP _ _ _ _ hpos A r₁ u₁ hf.complete hlA hb
  have hinj : Function.Injective (f.mapMatrix : M4 A →+* M4 𝔞.V) := Matrix.map_injective hf.inj
  have er : ∀ g, r g = f.mapMatrix (r₁ g) := fun g => by rw [← hr]; rfl
  have eu : u = f.mapMatrix u₁ := hu.symm
  have eV : ∀ g, mapRep f r' g = (1 + (z g).map f) * r g := fun g => by
    rw [rep_eq, e, map_mul, map_add, map_one, er]; rfl
  have hzV : ∀ g, (z g).map f ∈ uM 𝔞.V := fun g => uM_map f (hz g)
  have hyV := uM_map f hy
  have kill : ∀ g (B : ValuationSubring Ω), ¬ B.valuation (l : Ω) < 1 → g ∈ Ine (F := ℚ) B → r g = 1 → mapRep f r' g = 1 :=
    fun g B h1 h3 h4 => by
      have h5 : r₁ g = 1 := hinj (by rw [← er, h4, map_one])
      rw [eV, hN g ⟨h5, B, h1, h3⟩, h4]
      simp
  have fl : ∀ s ∈ D.Gp l, IsUp (adj ((1 - y.map f) * u) * mapRep f r' s * ((1 - y.map f) * u)) ∧
      ∀ i, (adj ((1 - y.map f) * u) * mapRep f r' s * ((1 - y.map f) * u) : M4 𝔞.V) i i = (adj u * r s * u : M4 𝔞.V) i i :=
    fun s hs => by
      rw [eV]
      refine twistFlag _ (r s) (r s⁻¹) _ _ u (hB s) (hB _) (by rw [← map_mul, inv_mul_cancel, map_one]) (hzV s) hyV hK.sp
        (hK.flag s hs) fun i j hij => ?_
      have h1 : adj u * ((z s).map f - (r s * y.map f * r s⁻¹ - y.map f)) * u =
          f.mapMatrix (adj u₁ * (z s - (r₁ s * y * r₁ s⁻¹ - y)) * u₁) := by
        rw [eu, er, er, adj_map]
        simp only [map_mul, map_sub]
        rfl
      rw [h1, RingHom.mapMatrix_apply, Matrix.map_apply, hfl s hs i j hij, map_zero]
  have eK : ∀ g, mapRep 𝔞.toK (mapRep f r') g = (1 + ((z g).map f).map 𝔞.toK) * mapRep 𝔞.toK r g := fun g => by
    rw [rep_eq, eV, map_mul, map_add, map_one]; rfl
  have hBK : ∀ g, IsBlock (mapRep 𝔞.toK r g) := fun g => blk_map 𝔞.toK (hB g)
  have hzK : ∀ g, ((z g).map f).map 𝔞.toK ∈ uM 𝔞.K := fun g => uM_map _ (hzV g)
  refine ⟨mapRep f r', (1 - y.map f) * u, ⟨⟨A, _, _, _, f, ⟨r', fun _ => (1 - y) * u₁⟩, hf, hc, ?_⟩, fun g i j => ?_, fun g => ?_,
    fun B hA g hg h1 => ?_, fun p hp g hg => ?_, ?_, fun s hs => (fl s hs).1, fun s hs i => ?_, fun s hs i => ?_⟩,
    ⟨fun g i j h => ?_, ?_, ?_⟩, fun g => ?_⟩
  · refine PD.ext rfl (funext fun _ => ?_)
    show f.mapMatrix ((1 - y) * u₁) = _
    rw [map_mul, map_sub, map_one, eu]; rfl
  · rw [eV, add_mul, one_mul, Matrix.add_apply, add_sub_right_comm]
    refine Ideal.add_mem _ (hK.red g i j) ?_
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (map_nonunit f _ (hm g i k))
  · rw [eV]
    exact (twistPt _ _ _ (hB g) (hzV g)).1 _ _ (hK.mult g)
  · exact kill g B (hA l (Finset.mem_insert_self _ _)) hg (hK.unr B hA g hg h1)
  · obtain ⟨h3, h4, -⟩ := (facts D hD).1 p hp
    exact kill g _ (not_over h3 hl.out h4.symm (hD.pl_over p h3)) hg.1 (hK.atP p hp g hg)
  · rw [sub_eq_add_neg]
    exact (twistPt _ _ _ (hB 1) (neg_mem hyV)).1 _ _ hK.sp
  · rw [(fl s hs).2]
    exact hK.char s hs i
  · rw [(fl s (Ine_le_Dec _ hs)).2]
    exact hK.inert s hs i
  · rw [eK]
    exact (twistPt _ _ _ (hBK g) (hzK g)).2.1 i j h
  · rw [show (fun g => (mapRep 𝔞.toK (mapRep f r') g).submatrix ixB ixB) = fun g => (mapRep 𝔞.toK r g).submatrix ixB ixB from
      funext fun g => by rw [eK]; exact (twistPt _ _ _ (hBK g) (hzK g)).2.2.1]
    refine spanB _ _ _ ⟨fun g => ⟨𝔞.toK (𝔞.a c (D.th g)), ?_⟩, hBK⟩ hsp
    have h1 := congrArg (𝔞.toK.mapMatrix : M4 𝔞.V →+* M4 𝔞.K) (hK.mult g)
    rw [map_mul, ← adj_map] at h1
    refine h1.trans ?_
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  · rintro ⟨Y, hY, hblk⟩
    have h3 : IsUnit (2 : 𝔞.K) := by have := h2.map 𝔞.toK; rwa [map_ofNat] at this
    have h4 := noCompl _ _ (mapRep 𝔞.toK r) (fun g => ((z g).map f).map 𝔞.toK) D.cc Y h3 hBK (fun g => (hzK g).1)
      (by rw [rep_eq, er, hb.cc]; exact (congrArg (·.map 𝔞.toK) (eAB_map f)).trans (eAB_map _))
      (by rw [hzc]; ext i j; simp) hY fun g => by rw [← eK]; exact hblk g
    refine hne (funext fun g => ?_)
    ext i j
    exact hf.inj (Subtype.ext (by simpa using congrFun (congrFun (h4 g) i) j))
  · rw [eV]
    exact (twistPt _ _ _ (hB g) (hzV g)).2.2.2
