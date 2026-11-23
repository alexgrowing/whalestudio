import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KillLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ExistsLocallyConstantDOneEqCocycleOfTameInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FrobDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem dec_unr {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {v : ℕ} (hv : v.Prime)
    (A : ValuationSubring Ω) (hA : A.valuation (v : Ω) < 1) :
    (∃ fr : Dec (F := ℚ) A,
      ((Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤) ∧
    ∀ m : ℕ, m ≠ 0 → ∃ U : Subgroup (Dec (F := ℚ) A), IsOpen (U : Set (Dec (F := ℚ) A)) ∧
      (Ine (F := ℚ) A).subgroupOf (Dec (F := ℚ) A) ≤ U ∧ U.index = m := by
  haveI : Fact v.Prime := ⟨hv⟩
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := v) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (Loc.decEmb (F := ℚ) (Ω := Ω) (v := v)).1 A w hAw hw
  obtain ⟨h1, h2, h3, -, -, -, -⟩ := Loc.iotaFacts (Ω := Ω) j
  have hmem : ∀ g, Loc.iota j g ∈ Dec (F := ℚ) (Loc.placeJ j) := fun g => h2 ▸ ⟨g, rfl⟩
  let f := (Loc.iota j).codRestrict (Dec (F := ℚ) (Loc.placeJ j)) hmem
  have hf : Topology.IsEmbedding f := h1.codRestrict _ hmem
  have hs : Function.Surjective f := fun g => by
    have : (g : G ℚ Ω) ∈ (Loc.iota j).range := by rw [h2]; exact g.2
    obtain ⟨s, hs⟩ := this
    exact ⟨s, Subtype.ext hs⟩
  let e := MulEquiv.ofBijective f ⟨hf.injective, hs⟩
  have hec' : Continuous e.symm := by
    rw [hf.isInducing.continuous_iff]
    have : (f ∘ e.symm) = id := funext fun g => e.apply_symm_apply g
    rw [this]
    exact continuous_id
  have hI : ∀ s, ((e s : ↥(Dec (F := ℚ) (Loc.placeJ j))) : G ℚ Ω) ∈ Ine (F := ℚ) (Loc.placeJ j) ↔ s ∈ Loc.Iq v :=
    fun s => by rw [← h3]; exact Iff.rfl
  obtain ⟨-, -, -, ⟨σ, hσ⟩, -⟩ := Loc.iqBasic v
  refine ⟨⟨f σ, ?_⟩, fun m hm => ?_⟩
  · have h := hs.denseRange.topologicalClosure_map_subgroup hf.continuous (Loc.frobDense σ hσ)
    rw [eq_top_iff, ← h]
    refine Subgroup.topologicalClosure_mono ?_
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    refine sup_le_sup_right ?_ _
    rintro _ ⟨s, hs', rfl⟩
    exact (hI s).2 hs'
  · haveI : NeZero m := ⟨hm⟩
    letI : TopologicalSpace (Multiplicative (ZMod m)) := ⊥
    haveI : DiscreteTopology (Multiplicative (ZMod m)) := ⟨rfl⟩
    obtain ⟨u, u1, u2, u3⟩ := Loc.frobFree σ hσ (Multiplicative (ZMod m)) (Multiplicative.ofAdd 1)
    have hu : Function.Surjective (u.comp e.symm.toMonoidHom) := fun y => by
      refine ⟨e (σ ^ (Multiplicative.toAdd y).val), ?_⟩
      simp [u3, ← ofAdd_nsmul]
    refine ⟨(u.comp e.symm.toMonoidHom).ker, ?_, fun g hg => ?_, ?_⟩
    · exact (isOpen_discrete {1}).preimage (u1.comp hec')
    · refine u2 _ ((hI _).1 ?_)
      have : e (e.symm.toMonoidHom g) = g := e.apply_symm_apply g
      rw [this]
      exact hg
    · rw [Subgroup.index_ker, MonoidHom.range_eq_top.2 hu]
      simp

private theorem norm_diag (O R : Type) [CommRing O] [CommRing R] [Algebra O R] {Γ : Type} [Group Γ] (ρ : Γ →* M4 R)
    (d : Γ → Fin 4 → R) (hρ : ∀ g, ρ g = Matrix.diagonal (d g)) (hd : ∀ g, d g 0 * d g 3 = d g 1 * d g 2) :
    (form O).Normalises ρ := by
  refine ⟨fun g => ⟨d g 0 * d g 3, ?_⟩, ⟨1, fun _ _ _ _ => rfl⟩, fun g a b h => ?_⟩
  · have hJ : (form O).JR R = J4 R := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [FormData.JR, form, J4]
    have := hd g
    rw [hJ, hρ, Matrix.diagonal_transpose]
    ext i j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    fin_cases i <;> fin_cases j <;> simp [J4] <;> first | linear_combination -this | ring
  · rw [hρ, Matrix.diagonal_apply_ne]
    rintro rfl
    exact h rfl

private theorem loc_diag (l : ℕ) [hl : Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (h2 : IsUnit (2 : O))
    (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    [T2Space Γ] (χ : Fin 4 → Γ →* Oˣ) (hχ : χ 0 * χ 3 = χ 1 * χ 2) (rbar : Γ →* M4 (ResidueField O))
    (r0 : Lift O rbar O) (h0 : r0.hom = diagRep χ) (hop : IsOpen (rbar.ker : Set Γ)) (I : Subgroup Γ) [I.Normal]
    (hI : IsClosed (I : Set Γ)) (hfr : ∃ fr : Γ, (I ⊔ Subgroup.zpowers fr).topologicalClosure = ⊤)
    (hU : ∀ n : ℕ, ∃ U : Subgroup Γ, IsOpen (U : Set Γ) ∧ I ≤ U ∧ U.index = l ^ n)
    (hN : ∀ n ∈ I ⊓ rbar.ker, r0.hom n = 1) :
    (form O).IsLocCond r0.hom (I ⊓ rbar.ker) (killCond rbar (I ⊓ rbar.ker : Subgroup Γ)) := by
  have hχ' : ∀ g, (χ 0 g : O) * χ 3 g = χ 1 g * χ 2 g := fun g => by
    simpa using congrArg (fun φ : Γ →* Oˣ => (φ g : O)) hχ
  have hrb : ∀ g, rbar g = Matrix.diagonal fun i => residue O (χ i g) := fun g => by
    ext a b
    have e : ∀ x : O, res O O x = residue O x := fun x => (res O O).commutes x
    rw [← r0.red, e, h0]
    show residue O (Matrix.diagonal (fun i => (χ i g : O)) a b) = _
    simp only [Matrix.diagonal_apply]
    split_ifs <;> simp
  have hbar : (form O).Normalises rbar := norm_diag O _ rbar _ hrb fun g => by
    simp only [← map_mul, hχ']
  refine kill_loc O _ _ _ (form O) h2 Γ rbar r0 hbar
    (norm_diag O O _ (fun g i => (χ i g : O)) (fun g => by rw [h0]; rfl) hχ') _ hN fun j => ?_
  have hk : rbar.ker ≤ (FormData.adRep hbar j).ker := fun g hg => by
    have h1 : rbar g = 1 := hg
    have h3 : rbar g⁻¹ = 1 := inv_mem hg
    refine LinearMap.ext fun Y => Subtype.ext ?_
    show rbar g * Y.1 * rbar g⁻¹ = Y.1
    rw [h1, h3, one_mul, mul_one]
  refine exists_locallyConstant_dOne_eq_cocycle_of_tame_inertia l (ResidueField O) Γ _ (FormData.adRep hbar j) (Subgroup.isOpen_mono hk hop) I _ hI
    (hI.inter (rbar.ker.isClosed_of_isOpen hop)) inf_le_left (inf_le_right.trans hk) ?_ hfr hU
  let t : Γ →* (Fin 4 → (ResidueField O)ˣ) :=
    Pi.monoidHom fun i => (Units.map (residue O : O →* ResidueField O)).comp (χ i)
  have ht : rbar.ker = t.ker := by
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hrb, ← Matrix.diagonal_one, Matrix.diagonal_injective.eq_iff]
    exact ⟨fun h => funext fun i => Units.ext (congrFun h i), fun h => funext fun i => congrArg Units.val (congrFun h i)⟩
  rw [Subgroup.inf_relIndex_left, ht, Subgroup.relIndex_ker]
  intro hd
  have h4 := hd.trans (Subgroup.card_subgroup_dvd_card (I.map t))
  rw [Nat.card_fun, Nat.card_units] at h4
  have h5 := hl.out.dvd_of_dvd_pow h4
  haveI := Fintype.ofFinite (ResidueField O)
  obtain ⟨n, -, hn⟩ := FiniteField.card (ResidueField O) l
  have h6 : l ∣ Nat.card (ResidueField O) := by
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self l n.ne_zero
  have h7 : 1 ≤ Nat.card (ResidueField O) := Nat.card_pos
  exact hl.out.not_dvd_one (Nat.sub_sub_self h7 ▸ Nat.dvd_sub h6 h5)

theorem UpperTheory.V.GradeZeroInterpolatingElement.locCondQ :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ (rb : D.Gam →* M4 (ResidueField c.O)) (r0 : Lift c.O rb c.O), rb.comp (toGS Ω D.SP) = D.rbar → r0.hom.comp (toGS Ω D.SP) = D.r0 → ∀ q : D.frame.Q, (form c.O).IsLocCond (r0.hom.comp (D.frame.ψ q)) (D.frame.N q) (killCond (rb.comp (D.frame.ψ q)) (D.frame.N q)) := by
  intro Ω _ _ _ l hl c D hD rb r0 hrb hr0 ⟨q, hq⟩
  obtain ⟨hqS, hqT⟩ := Finset.mem_sdiff.1 hq
  have hqp := hD.S_prime q hqS
  have hA := hD.pl_over q hqp
  obtain ⟨f1, -, f3, -, -, f6, -, -, -, -, -, f12, -⟩ := facts D hD
  obtain ⟨-, hfin, hlm, -⟩ := abelian₂.dvr_finite l c.O
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact hlm)
  have h2 : IsUnit (2 : c.O) := by
    obtain ⟨-, -, -, -, -, -, -, -, h⟩ := dvrFacts l c.O
    exact_mod_cast h 2 fun hd => hD.l_odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 hd)
  haveI : IsGalois ℚ Ω := {}
  haveI : CompactSpace (D.Gp q) := isCompact_iff_compactSpace.1 (isClosed_Dec _).isCompact
  obtain ⟨hfr, hU⟩ := dec_unr hqp (D.pl q) hA
  have e1 : rb.comp (locHom D.SP (D.pl q)) = D.rbar.comp (D.Gp q).subtype := by rw [← hrb]; rfl
  have e2 : r0.hom.comp (locHom D.SP (D.pl q)) = D.r0.comp (D.Gp q).subtype := by rw [← hr0]; rfl
  have e3 : (D.Ip q ⊓ D.rbar.ker).subgroupOf (D.Gp q) =
      (D.Ip q).subgroupOf (D.Gp q) ⊓ (rb.comp (locHom D.SP (D.pl q))).ker := by
    rw [e1]; rfl
  have hAw : Raw.Away D.T (D.pl q) := fun p hp hv => by
    have hpp : p.Prime := by
      rcases Finset.mem_insert.1 hp with rfl | h
      · exact hl.out
      · exact (f1 p h).1
    have hc : IsCoprime (p : ℤ) (q : ℤ) :=
      Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hpp hqp).2 fun h => hqT (h ▸ hp))
    obtain ⟨a, b, hab⟩ := hc
    have hi : ∀ n : ℤ, (D.pl q).valuation (n : Ω) ≤ 1 := fun n =>
      ((D.pl q).valuation_le_one_iff _).mpr (intCast_mem _ n)
    have h1 : (D.pl q).valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi a)) hv
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hi b)) hA
    have h3 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
    rw [h3, map_one] at h1
    exact lt_irrefl _ h1
  have key := loc_diag l c.O h2 (D.Gp q) (fun i => (D.ps i).comp (D.Gp q).subtype)
    (by
      have := (f6 0).trans (f6 1).symm
      exact congrArg (fun φ => MonoidHom.comp φ (D.Gp q).subtype) this)
    (rb.comp (locHom D.SP (D.pl q))) (r0.comap _ (continuous_locHom D.SP (D.pl q))) e2
    (by rw [e1]; exact f12.preimage continuous_subtype_val) ((D.Ip q).subgroupOf (D.Gp q))
    ((isClosed_Ine _).preimage continuous_subtype_val) hfr (fun n => hU _ (pow_ne_zero n hl.out.ne_zero))
    (by
      rw [← e3]
      intro n hn
      have h1 : ∀ i, D.ps i n = 1 := fun i => f3 i _ hAw _ hn.1 hn.2
      refine (DFunLike.congr_fun e2 n).trans ?_
      show Matrix.diagonal (fun i => (D.ps i n : c.O)) = 1
      simp [h1])
  rw [← e3] at key
  exact key
