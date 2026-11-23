import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondSelmerSpanBoundAtAllLevels
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGmap
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DOfRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RrGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OoMaps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpRoots
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem chi_rep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly, Matrix.charmatrix]
  congr 2
  · ext1 a b
    by_cases hab : a = b <;> simp [GDet.repAlg, hab, Matrix.one_apply, Matrix.diagonal_apply]
  · ext1 a b
    simp [GDet.repAlg]

private theorem inj_of_prod {n : ℕ} {A : Type} [CommRing A] [IsDomain A] {a b : Fin n → A}
    (h : ∏ i, (Polynomial.X - Polynomial.C (a i)) = ∏ i, (Polynomial.X - Polynomial.C (b i)))
    (hb : Function.Injective b) : Function.Injective a := by
  have e : ∀ c : Fin n → A, (∏ i, (Polynomial.X - Polynomial.C (c i))).roots = Finset.univ.val.map c := fun c => by
    rw [← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map c), Multiset.map_map]
    rfl
  have h1 : Finset.univ.val.map a = Finset.univ.val.map b := by rw [← e, ← e, h]
  have h2 : (Finset.univ.val.map a).Nodup := h1 ▸ Finset.univ.nodup.map hb
  exact fun i j hij => Multiset.inj_on_of_nodup_map h2 i (Finset.mem_univ_val i) j (Finset.mem_univ_val j) hij

private theorem lam_lift {n : ℕ} {R S H G : Type} [CommRing R] [CommRing S] [Group H] [Group G]
    {E : GDet n R H} {D : GDet n S G} {f : R →+* S} {φ : H →* G}
    (h : D.comap φ = E.map f) (i : ℕ) (y : MonoidAlgebra R H) :
    D.lam i (MonoidAlgebra.mapDomainRingHom S φ (MonoidAlgebra.mapRingHom H f y)) = f (E.lam i y) := by
  rw [← ((UpperTheory.V.CA.d_gmap E).2.2.1 f y).2 i, ← h]
  unfold GDet.lam
  generalize MonoidAlgebra.mapRingHom H f y = z
  congr 2
  change D.D (Polynomial S) _ = D.D (Polynomial S) (MonoidAlgebra.mapDomainRingHom (Polynomial S) φ _)
  congr 1
  rw [map_sub]
  congr 1
  · simp
  · induction z using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | single g r => simp

private theorem rep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H]
    (ρ : G →* Matrix (Fin n) (Fin n) A) (φ : H →* G) : (GDet.ofRep ρ).comap φ = GDet.ofRep (ρ.comp φ) := by
  refine GDet.ext fun S _ _ z => ?_
  change (GDet.repAlg ρ S (MonoidAlgebra.mapDomainRingHom S φ z)).det = (GDet.repAlg (ρ.comp φ) S z).det
  congr 1
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single g r => simp [GDet.repAlg]

private theorem genBy_img {O R S : Type} [CommRing O] [CommRing R] [Algebra O R] [IsLocalRing R] [CommRing S]
    [Algebra O S] [IsLocalRing S] (f : R →ₐ[O] S) (hf : Function.Surjective f) {s : Set R} {t : Set S}
    (h : GenBy O s) (hst : ∀ a ∈ s, f a ∈ t) : GenBy O t := by
  intro N b
  obtain ⟨b, rfl⟩ := hf b
  obtain ⟨a, ha, hb⟩ := h N b
  haveI : IsLocalHom (f : R →+* S) := IsLocalHom.of_surjective _ hf
  refine ⟨f a, ?_, ?_⟩
  · have : Algebra.adjoin O s ≤ (Algebra.adjoin O t).comap f :=
      Algebra.adjoin_le fun c hc => Algebra.subset_adjoin (hst c hc)
    exact this ha
  · rw [← map_sub]
    have h1 : (maximalIdeal R).map (f : R →+* S) ≤ maximalIdeal S :=
      Ideal.map_le_iff_le_comap.2 fun c hc => map_nonunit (f : R →+* S) c hc
    have h2 := Ideal.mem_map_of_mem (f : R →+* S) hb
    rw [Ideal.map_pow] at h2
    exact Ideal.pow_right_mono h1 N h2

theorem UpperTheory.V.Pa.Core.ooPt :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (Λ : Lim T) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (r : Resid G0.frame O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B) (J : Ideal B) (D : ℕ) (A : TWAut u J Unit D T) (W : RRObj Λ A) (m : RMaps W) [IsCO O (W.R ⧸ ii W)] (o : OoPair W) (πb : (W.R ⧸ ii W) →ₐ[O] Spo A), (∀ a, πb (Ideal.Quotient.mk (ii W) a) = m.π a) → Adapted T (r := r) → ∀ (D0 : ℕ) (x : Pt T u D0) (x' : Spo A →ₐ[O] x.x.A), (∀ b, x' (algebraMap B (Spo A) b) = x.f b) → Function.Surjective (algebraMap O x.x.K) → x.f (A.b.lam (MvPowerSeries.X (.inl ()))) = x.x.t → x' (m.π (fo W)) ≠ 0 ∧ ∃ P : OoPt Λ.h x.x o.p, P.f = x'.comp πb ∧ P.ker = ooKer o := by
  intro l _ L G0 T Λ n O _ _ _ _ _ r B _ _ _ u J D A W m _ o πb hπ had D0 x x' hx' hsurj ht
  obtain ⟨-, -, hs, hU, hy⟩ := m.π_maps
  obtain ⟨hD, hψ⟩ := ooMaps l L G0 T Λ n O r B u J D A W m o πb hπ
  have hc : x'.toRingHom.comp (algebraMap B (Spo A)) = x.f.toRingHom := RingHom.ext hx'
  have heig : ∀ j, (mat x.x.ρ (T.sg j)).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (x' (m.π (W.t.U j i)))) := fun j => by
    have h1 := congrArg (Polynomial.map x'.toRingHom) (spRoots B T.q n
      (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) (fun j i => algebraMap O B (A.ut j i)) j).1
    rw [Polynomial.map_map, hc, ← ((UpperTheory.V.CA.d_gmap u.D).2.2.1 _ _).1, x.maps.1, MonoidAlgebra.mapRingHom_single,
      map_one, chi_rep, Polynomial.map_prod] at h1
    rw [← h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact congrArg (fun a => Polynomial.X - Polynomial.C (x' a)) (hU j i).symm
  have hinj : ∀ j, Function.Injective fun i => x' (m.π (W.t.U j i)) := fun j =>
    inj_of_prod ((heig j).symm.trans (x.eig j).2) (x.eig j).1
  have hl := lam_lift o.D_eq
  set Φ : MonoidAlgebra W.R (Ph0 Λ) →+* MonoidAlgebra (W.R ⧸ ii W) Λ.G.G₀ :=
    (MonoidAlgebra.mapDomainRingHom _ (πo0 Λ)).comp (MonoidAlgebra.mapRingHom _ (Ideal.Quotient.mk (ii W))) with hΦ
  have hp : ∀ g a, Φ (MonoidAlgebra.single g a) = MonoidAlgebra.single (πo0 Λ g) (Ideal.Quotient.mk (ii W) a) :=
    fun g a => by simp [hΦ]
  have hl' : ∀ i y, o.p.D.lam i (Φ y) = Ideal.Quotient.mk (ii W) (W.t.D.lam i y) := hl
  have hrel : ∀ y, Rel W (W.t.D.tr y) → o.p.D.tr (Φ y) = 0 := fun y h =>
    (hl' 1 y).trans (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span h))
  have hsj : Function.Surjective (πo0 Λ) := Λ.πo0_surj
  refine ⟨?_, ⟨{
      fg := ?_, Ip := fun w => ?_, surj := hsurj, q := T.q, ph := Λ.ph, ta := Λ.ta, comm := Λ.comm, p_ta := Λ.p_ta
      U := fun j i => Ideal.Quotient.mk (ii W) (W.t.U j i), y := fun j i => Ideal.Quotient.mk (ii W) (W.t.y j i)
      s := Ideal.Quotient.mk (ii W) W.t.s, q1 := fun j g => ?_, q2 := fun j i g => ?_, gen := ?_
      f := x'.comp πb, maps := ⟨?_, fun v i => ?_⟩, f_s := ?_, f_y := fun j i => ?_, f_U := fun j => ?_
      eig := fun j => ?_ }, rfl, rfl⟩⟩
  · simp only [fo, fEl, map_prod, map_mul, map_sub, Nat.cast_one, one_mul]
    refine Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      Finset.prod_ne_zero_iff.2 fun i' hi' => ?_
    have := sub_ne_zero.2 ((hinj j).ne (Finset.ne_of_mem_erase hi').symm)
    exact mul_ne_zero this this
  · classical
    obtain ⟨s, hs⟩ := Λ.fg
    refine ⟨s.image Λ.πo, ?_⟩
    rw [Finset.coe_image, ← MonoidHom.map_closure]
    exact Λ.πo_surj.denseRange.topologicalClosure_map_subgroup Λ.πo_cont hs
  · refine inf_eq_left.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    refine Subgroup.mem_iInf.2 fun i => ?_
    have h1 : G0.φu w g ∈ r.Ip w := by rw [had.2]; exact ⟨g, hg, rfl⟩
    have h2 := Subgroup.mem_iInf.1 h1.2 i
    rw [o.compat.1 i]
    change r.chib i (Λ.h.p₀ (Λ.G.φu w g)) = 1
    rw [Λ.h.p₀_φu]
    exact h2
  · obtain ⟨g, rfl⟩ := hsj g
    obtain ⟨ph, hph⟩ := hsj (Λ.ph j)
    have := hrel _ (Rel.q1 j ph g hph)
    rw [map_mul, hp, map_one, q1El, map_list_prod, List.map_ofFn] at this
    refine Eq.trans ?_ this
    rw [q1El]
    congr 4
    funext i
    simp only [Function.comp_apply, map_sub, hp, map_one, hph]
  · obtain ⟨g, rfl⟩ := hsj g
    obtain ⟨ph, hph⟩ := hsj (Λ.ph j)
    obtain ⟨ta, hta⟩ := hsj (Λ.ta j)
    have := hrel _ (Rel.q2 j i ph ta g hph hta)
    rw [map_mul, hp, map_one, q2El, map_mul, map_list_prod, List.map_ofFn, map_sub, map_sub, hp, hp, hta] at this
    simp only [map_one] at this
    refine Eq.trans ?_ this
    rw [q2El]
    congr 5
    funext k
    by_cases hk : k = i <;> simp only [Function.comp_apply, map_sub, hp, map_one, hph, hk, if_true, if_false]
  · refine genBy_img (Ideal.Quotient.mkₐ O (ii W)) Ideal.Quotient.mk_surjective
      (rrGen l L G0 T Λ n O r B u J D A W) ?_
    rintro a (((⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩) | ⟨j, i, h⟩) | rfl)
    · refine Or.inl (Or.inl (Or.inl ⟨i, πo0 Λ g, ?_⟩))
      have := hl' i (MonoidAlgebra.single g 1)
      rw [hp, map_one] at this
      exact this.symm
    · refine Or.inl (Or.inl (Or.inr ⟨v, i, g, ?_⟩))
      rw [o.ψ_eq]
      rfl
    · exact Or.inl (Or.inr ⟨j, i, h.imp (congrArg _) (congrArg _)⟩)
    · exact Or.inr rfl
  · have e : (x'.comp πb).toRingHom = x'.toRingHom.comp πb.toRingHom := rfl
    rw [e, ← (UpperTheory.V.CA.d_gmap o.p.D).2.1, hD, (UpperTheory.V.CA.d_gmap _).2.1, hc]
    change (u.D.map x.f.toRingHom).comap Λ.h.p₀ = _
    rw [x.maps.1, rep_comap]
    rfl
  · rw [← x.maps.2 v i, ← hc]
    exact congrArg (pushCh x'.toRingHom) (hψ v i)
  · rw [AlgHom.comp_apply, hπ, ← ht, ← hx']
    exact congrArg x' hs
  · rw [AlgHom.comp_apply, hπ, ← map_zero x']
    exact congrArg x' (hy j i)
  · simpa only [AlgHom.comp_apply, hπ] using hinj j
  · simpa only [AlgHom.comp_apply, hπ, Λ.p_ph] using heig j
