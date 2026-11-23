import Development.EtaleCohomology.TateTwists.EtaleTateTwistLocalGenerationAndRootCompatOfPart

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem ofRings_sec_res {R : Type} [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R))
    {V U : Scheme.{0}} (g : V ⟶ U) (x : M.obj Γ(U, ⊤)) :
    Sec.res g (ofRings.sec M U x) = ofRings.sec M V ((M.map g.appTop).hom x) := by
  have h := (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ M)).naturality g.op
  have h2 := congrArg (fun f => f.hom x) h
  simp only [ModuleCat.hom_comp] at h2
  exact h2.symm

theorem res_twGen (q : ℕ) (j : ℤ) {V U : Scheme.{0}} (g : V ⟶ U) (ζ : Prim q Γ(U, ⊤)) :
    Sec.res g (twGen j ζ) = twGen j (ζ.map g.appTop.hom) := by
  refine (ofRings_sec_res (twF q j) g _).trans ?_
  congr 1
  change Submodule.mapQ _ _ _ (twRel_le q j (Scheme.Hom.appTop g).hom) (Submodule.Quotient.mk _) = _
  rw [Submodule.mapQ_apply]
  simp [Finsupp.mapDomain_single]

theorem twGen_pow (q : ℕ) [NeZero q] (j : ℤ) {V : Scheme.{0}} (ζ ξ : Prim q Γ(V, ⊤)) (a : (ZMod q)ˣ)
    (h : ξ.1 = ζ.1 ^ (a : ZMod q).val) :
    twGen j ξ = ((a ^ j : (ZMod q)ˣ) : ZMod q).val • twGen j ζ := by
  have hrel : (Submodule.Quotient.mk (Finsupp.single ξ 1) : (twF q j).obj Γ(V, ⊤)) =
      Submodule.Quotient.mk (Finsupp.single ζ (ULift.up ((a ^ j : (ZMod q)ˣ) : ZMod q))) := by
    rw [Submodule.Quotient.eq]
    exact Submodule.subset_span ⟨ζ, ξ, a, h, rfl⟩
  have hs : (Finsupp.single ζ (ULift.up ((a ^ j : (ZMod q)ˣ) : ZMod q)) : Prim q Γ(V, ⊤) →₀ ULift.{1} (ZMod q)) =
      ((a ^ j : (ZMod q)ˣ) : ZMod q).val • Finsupp.single ζ 1 := by
    rw [Finsupp.smul_single]
    congr 1
    apply ULift.ext
    simp only [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val _).symm
  have key : ∀ (n : ℕ) (x y : (twF q j).obj Γ(V, ⊤)), x = n • y →
      ofRings.sec (twF q j) V x = n • ofRings.sec (twF q j) V y := by
    rintro n x y rfl
    exact map_nsmul _ _ _
  refine key _ _ _ ?_
  show (Submodule.Quotient.mk (Finsupp.single ξ 1) : (_ ⧸ twRel q j Γ(V, ⊤))) =
    _ • (Submodule.Quotient.mk (Finsupp.single ζ 1) : (_ ⧸ twRel q j Γ(V, ⊤)))
  rw [hrel, hs]
  exact map_nsmul (Submodule.mkQ _) _ _

end LateralTheory.EtaleFoundations.GenIsoSurjRootPf

def LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther : Prop :=
  ∀ (q : ℕ) [NeZero q] (U : Scheme.{0}) (ζ ξ : Prim q Γ(U, ⊤)),
    Loc U fun _ g => ∃ a : (ZMod q)ˣ, g.appTop.hom ξ.1 = g.appTop.hom ζ.1 ^ (a : ZMod q).val

open LateralTheory.EtaleFoundations.GenIsoSurjRootPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_root_change_of_local_primitive_root_powers
    (hp : LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther) :
    LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange := by
  intro q _ j
  refine ⟨fun V U g ζ => res_twGen q j g ζ, fun U ζ ξ => ?_⟩
  obtain ⟨S, hS, h⟩ := hp q U ζ ξ
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨a, ha⟩ := h V g hg
  exact ⟨_, (res_twGen q j g ξ).trans (twGen_pow q j (ζ.map g.appTop.hom) (ξ.map g.appTop.hom) a ha)⟩

namespace LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem alg_prim_pow {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) (ζ ξ : A)
    (hζ : Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0) (hξ : Polynomial.aeval ξ (Polynomial.cyclotomic q ℤ) = 0)
    {K : Type} [Field K] (f : A →+* K) : ∃ (a : (ZMod q)ˣ) (s : A), f s ≠ 0 ∧ s * (ξ - ζ ^ (a : ZMod q).val) = 0 := by
  have hqK : (q : K) ≠ 0 := by
    have := hq.map f; simpa using this.ne_zero
  have : NeZero (q : K) := ⟨hqK⟩
  have root : ∀ x : A, Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0 → IsPrimitiveRoot (f x) q := by
    intro x hx
    rw [← Polynomial.isRoot_cyclotomic_iff, ← Polynomial.map_cyclotomic_int, Polynomial.IsRoot.def,
      Polynomial.eval_map]
    have h1 := congrArg f hx
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at h1
    rwa [show f.comp (algebraMap ℤ A) = Int.castRingHom K from RingHom.ext_int _ _] at h1
  have pq : ∀ x : A, Polynomial.aeval x (Polynomial.cyclotomic q ℤ) = 0 → x ^ q = 1 := by
    intro x hx
    obtain ⟨r, hr⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one q ℤ
    have := congrArg (Polynomial.aeval x) hr
    rw [map_mul, hx, zero_mul] at this
    simpa [sub_eq_zero] using this
  obtain ⟨i, hi, he⟩ := (root ζ hζ).eq_pow_of_pow_eq_one (root ξ hξ).pow_eq_one
  have hcop : i.Coprime q := by
    have h2 := root ξ hξ
    rw [← he] at h2
    exact ((root ζ hζ).pow_iff_coprime (NeZero.pos q) i).1 h2
  refine ⟨ZMod.unitOfCoprime i hcop, ∑ m ∈ Finset.range q, ξ ^ m * (ζ ^ i) ^ (q - 1 - m), ?_, ?_⟩
  · have hv : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    intro h0
    rw [map_sum] at h0
    have : ∀ m ∈ Finset.range q, f (ξ ^ m * (ζ ^ i) ^ (q - 1 - m)) = (f ζ ^ i) ^ (q - 1) := by
      intro m hm
      rw [map_mul, map_pow, map_pow, map_pow, ← he, ← pow_add]
      congr 1
      have := Finset.mem_range.1 hm; omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h0
    rcases mul_eq_zero.1 h0 with h | h
    · exact hqK h
    · exact (root ζ hζ).ne_zero (NeZero.ne q) (eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero h))
  · have hv : ((ZMod.unitOfCoprime i hcop : (ZMod q)ˣ) : ZMod q).val = i := by
      rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
    rw [hv, geom_sum₂_mul]
    rw [pq ξ hξ, ← pow_mul, mul_comm i q, pow_mul, pq ζ hζ, one_pow, sub_self]

theorem unit_res {U : Scheme.{0}} (s : Γ(U, ⊤)) : ∀ (O : U.Opens) (h : O ≤ ⊤), O = U.basicOpen s →
    IsUnit (U.presheaf.map (homOfLE h).op s) := by
  rintro O h rfl
  exact RingedSpace.isUnit_res_basicOpen U.toRingedSpace s

theorem loc_of_points {U : Scheme.{0}} (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g))
    (h : ∀ x : U, ∃ s : Γ(U, ⊤), x ∈ U.basicOpen s ∧ P _ (U.basicOpen s).ι) : Loc U P := by
  choose s hs hPs using h
  let S : Sieve U := { arrows := fun V g => P V g, downward_closed := fun hg k => hP _ _ _ k hg }
  refine ⟨S, Scheme.zariskiTopology_le_etaleTopology _ ?_, fun V g hg => hg⟩
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨U.openCoverOfIsOpenCover (fun x => U.basicOpen (s x)) ?_, ?_⟩
  · exact eq_top_iff.2 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hs x⟩
  · rintro V g ⟨x⟩
    exact hPs x

theorem prim_root_loc : LateralTheory.EtaleFoundations.EtalePrimitiveRootsLocallyPowersOfEachOther := by
  intro q _ U ζ ξ
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  refine loc_of_points _ ?_ fun x => ?_
  · rintro V W g k ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [Scheme.Hom.comp_appTop]
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, ha, map_pow]
  · obtain ⟨a, s, hs, hd⟩ := alg_prim_pow q hq ζ.1 ξ.1 ζ.2.2 ξ.2.2 (U.Γevaluation x).hom
    refine ⟨s, (U.evaluation_ne_zero_iff_mem_basicOpen x (show x ∈ (⊤ : U.Opens) from trivial) s).1 hs, a, ?_⟩
    have hu : IsUnit ((U.basicOpen s).ι.appTop.hom s) := unit_res s _ _ (by simp)
    have h0 := congrArg (U.basicOpen s).ι.appTop.hom hd
    rw [map_mul, map_zero, map_sub, map_pow] at h0
    exact sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)

end LateralTheory.EtaleFoundations.GenIsoSurjRootPf

theorem LateralTheory.EtaleFoundations.etale_tate_twist_generator_restriction_and_root_change_holds : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorRestrictionAndRootChange :=
  LateralTheory.EtaleFoundations.etale_tate_twist_generator_root_change_of_local_primitive_root_powers LateralTheory.EtaleFoundations.GenIsoSurjRootPf.prim_root_loc
