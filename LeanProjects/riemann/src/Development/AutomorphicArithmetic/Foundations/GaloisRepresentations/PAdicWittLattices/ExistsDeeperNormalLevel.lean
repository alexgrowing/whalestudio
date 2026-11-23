import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharZeroGenericModelNonemptyStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

section SlopeTestRemainingChoices

open GlobalTheory.KS GlobalTheory.KS.PowPB

private theorem powMap_congr' {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f f' : S' ⟶ S}
    {φ φ' : A'.left ⟶ A.left} (hf : f = f') (hφ : φ = φ') (h : φ ≫ A.hom = A'.hom ≫ f)
    (h' : φ' ≫ A.hom = A'.hom ≫ f') (m : ℕ) : powMap f φ h m = powMap f' φ' h' m := by
  subst hf hφ; rfl

private theorem powMap_id' {S : Scheme.{0}} (A : Over S) (h : 𝟙 A.left ≫ A.hom = A.hom ≫ 𝟙 S) (m : ℕ) :
    powMap (𝟙 S) (𝟙 A.left) h m = 𝟙 _ := by
  apply pow_left_hom_ext
  · rw [powMap_w, Category.comp_id, Category.id_comp]
  · intro i
    rw [powMap_pr, Category.comp_id, Category.id_comp]

private theorem powMap_comp' {S S' S'' : Scheme.{0}} {A : Over S} {A' : Over S'} {A'' : Over S''}
    (f : S' ⟶ S) (g : S'' ⟶ S') (φ : A'.left ⟶ A.left) (χ : A''.left ⟶ A'.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (h' : χ ≫ A'.hom = A''.hom ≫ g)
    (h'' : (χ ≫ φ) ≫ A.hom = A''.hom ≫ g ≫ f) (m : ℕ) :
    powMap g χ h' m ≫ powMap f φ h m = powMap (g ≫ f) (χ ≫ φ) h'' m := by
  apply pow_left_hom_ext
  · rw [Category.assoc, powMap_w, ← Category.assoc, powMap_w, powMap_w, Category.assoc]
  · intro i
    rw [Category.assoc, powMap_pr, ← Category.assoc, powMap_pr, powMap_pr, Category.assoc]

private theorem powMap_ext' {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (π : S' ⟶ S) (Φ : A'.left ⟶ A.left)
    (w : Φ ≫ A.hom = A'.hom ≫ π) (π' : S' ⟶ S') (Φ' : A'.left ⟶ A'.left) (w' : Φ' ≫ A'.hom = A'.hom ≫ π') (m : ℕ)
    (pb : IsPullback (powMap π Φ w m) (pow A' m).hom (pow A m).hom π) {T : Scheme.{0}} (x y : T ⟶ (pow A' m).left)
    (hxy : x ≫ powMap π Φ w m = y ≫ powMap π Φ w m) (h1 : (x ≫ (pow A' m).hom) ≫ π' = y ≫ (pow A' m).hom)
    (h2 : ∀ a : T ⟶ A'.left, a ≫ A'.hom = x ≫ (pow A' m).hom → a ≫ Φ' ≫ Φ = a ≫ Φ) :
    y = x ≫ powMap π' Φ' w' m := by
  have e1 : x ≫ (pow A' m).hom ≫ π' ≫ π = x ≫ (pow A' m).hom ≫ π := by
    have := congrArg (· ≫ (pow A m).hom) hxy
    simp only [Category.assoc, powMap_w] at this
    rw [← Category.assoc y, ← h1] at this
    simpa only [Category.assoc] using this.symm
  apply pb.hom_ext
  · rw [← hxy, Category.assoc]
    apply pow_left_hom_ext
    · simp only [Category.assoc, powMap_w, reassoc_of% (powMap_w π' Φ' w' m)]
      exact e1.symm
    · intro i
      simp only [Category.assoc, powMap_pr, reassoc_of% (powMap_pr π' Φ' w' m i)]
      have := h2 (x ≫ (pr A' i).left) (by rw [Category.assoc, Over.w])
      simpa only [Category.assoc] using this.symm
  · rw [Category.assoc, powMap_w, ← Category.assoc, h1]

end SlopeTestRemainingChoices

section Lat

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p}

private def intSub (L : Link D G) : Submonoid G.GAf where
  carrier := {h | Integ L h}
  one_mem' := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
  mul_mem' := UpperTheory.Gal.Int.Geo.Integ.mul

private theorem exists_deeper_normal_level (hK : KNBasic) (L : Link D G) (j : Lv p) (S : Finset (Lv p × G.GAf)) :
    ∃ m : Lv p, L.KN m.1 ≤ L.KN j.1 ∧ (∀ κ ∈ L.KN j.1, ∀ u ∈ L.KN m.1, κ * u * κ⁻¹ ∈ L.KN m.1) ∧
      ∀ x ∈ S, ∀ u ∈ L.KN m.1, x.2 * u * x.2⁻¹ ∈ L.KN x.1.1 := by
  classical
  choose c hc hadm using fun (N : ℕ) (g : G.GAf) => (hK p D G L N).2.1 g
  set M : ℕ := j.1 * ∏ x ∈ S, (x.1.1 * c x.1.1 x.2) with hMdef
  have hcop : M.Coprime p :=
    Nat.Coprime.mul j.2.2 (Nat.Coprime.prod_left fun x _ => Nat.Coprime.mul x.1.2.2 (hc _ _))
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · rw [h, Nat.coprime_zero_left] at hcop
      exact absurd hcop (Fact.out : p.Prime).one_lt.ne'
    · exact h
  have hjM : j.1 ∣ M := dvd_mul_right _ _
  refine ⟨⟨M, le_trans j.2.1 (Nat.le_of_dvd hM0 hjM), hcop⟩, UpperTheory.Gal.Int.Geo.KN_anti hjM, ?_, ?_⟩
  · intro κ hκ u hu
    exact (hK p D G L M).1 κ (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hκ) u hu
  · intro x hx u hu
    have hd : x.1.1 * c x.1.1 x.2 ∣ M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ hx) _
    exact hadm x.1.1 x.2 u (UpperTheory.Gal.Int.Geo.KN_anti hd hu)

end Lat

private theorem comp_univ_hom_eq_of_wit {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {R : Type}
    [CommRing R] [Algebra ℚ R] {gb : GBase D.toG R} {h : G.GAf} {N N' : ℕ} {X' : GenModel gb N'}
    {X : GenModel gb N} {π : X'.X ⟶ X.X} {Φ : X'.univ.A.left ⟶ X.univ.A.left} (hW : Wit L h X' X π Φ) :
    Φ ≫ X.univ.A.hom = X'.univ.A.hom ≫ π := by
  obtain ⟨-, o, ψ, φ, -, rfl⟩ := hW
  rw [Category.assoc, φ.cart.1.w, ← Category.assoc, Over.w]

theorem UpperTheory.Gal.G3.pKSEx :
    KNBasic → WitUniq → WitComp → WitCart → WitEx → WitOne → WitTrans → WitFree → KSEx := by
  intro hK hU hC hCart hEx hOne hTr hFree p _ D G L _ R _ _ gb k
  have hM : ∀ N : Lv p, Nonempty (GenModel gb N.1) := fun N => GlobalTheory.T.unitaryCharZeroGenericModel_nonempty p D R gb N.1 N.2.1 N.2.2
  let M : (N : Lv p) → GenModel gb N.1 := fun N => (hM N).some
  have hint : ∀ {N : ℕ} {u : G.GAf}, u ∈ L.KN N → Integ L u := fun hu =>
    UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu)
  have hw : ∀ (N' N : Lv p) (h : G.GAf), Integ L h → AdmK L N'.1 N.1 h →
      ∃ (π : (M N').X ⟶ (M N).X) (Φ : (M N').univ.A.left ⟶ (M N).univ.A.left), Wit L h (M N') (M N) π Φ :=
    fun N' N h a b => hEx p D G L R gb M N' N h a b
  choose πc Φc hWc using hw
  have hpb : ∀ (i j : Lv p) (a : Integ L 1) (b : AdmK L i.1 j.1 1),
      IsPullback (GlobalTheory.KS.powMap (πc i j 1 a b) (Φc i j 1 a b) (comp_univ_hom_eq_of_wit (hWc i j 1 a b)) k)
        (GlobalTheory.KS.pow (M i).univ.A k).hom (GlobalTheory.KS.pow (M j).univ.A k).hom (πc i j 1 a b) := fun i j a b =>
    GlobalTheory.KS.PowPB.powMap_isPullback _ _ _ _ _ _ _
      (hCart p D G L R gb i.1 j.1 (M i) (M j) 1 (one_mem _) _ _ (hWc i j 1 a b)) k
  let T : Tower (Sp R) G.GAf :=
    Tower.mk (Lv p)
      (K := fun N => L.KN N.1)
      (Δ := intSub L)
      (K_le := fun _ _ hk => hint hk)
      (deep := fun j S => exists_deeper_normal_level hK L j S)
      (idx := fun i j => (hK p D G L j.1).2.2 i.1 (by have := j.2.1; omega) (by have := i.2.1; omega))
      (Z := fun N => (GlobalTheory.KS.pow (M N).univ.A k).left)
      (q := fun N => (GlobalTheory.KS.pow (M N).univ.A k).hom ≫ (M N).s)
      (tr := fun i j h a b => GlobalTheory.KS.powMap (πc i j h a b) (Φc i j h a b) (comp_univ_hom_eq_of_wit (hWc i j h a b)) k)
      (tr_q := by
        intro i j h a b
        rw [← Category.assoc, GlobalTheory.KS.PowPB.powMap_w, Category.assoc, (hWc i j h a b).1])
      (tr_self := by
        intro i u a b hu
        have hid := (hC p D G L R gb i i i (M i) (M i) (M i) u u).1 u hu
        obtain ⟨e1, e2⟩ := hU p D G L R gb i i (M i) (M i) u a b _ _ _ _ (hWc i i u a b) hid
        exact (powMap_congr' e1 e2 _ (by simp) k).trans (powMap_id' _ _ k))
      (tr_mul := by
        intro i j m h h' a b a' b' a'' b''
        have hcomp := (hC p D G L R gb i j m (M i) (M j) (M m) h h').2 a' b' _ _ _ _ (hWc i j h a b) (hWc j m h' a' b')
        obtain ⟨e1, e2⟩ := hU p D G L R gb i m (M i) (M m) (h' * h) a'' b'' _ _ _ _ hcomp (hWc i m (h' * h) a'' b'')
        exact (powMap_comp' _ _ _ _ _ _ (comp_univ_hom_eq_of_wit hcomp) k).trans (powMap_congr' e1 e2 _ _ k))
      (fin := by
        intro i j a b
        exact MorphismProperty.of_isPullback (P := @IsFinite) (hpb i j a b).flip
          (hOne p D G L R gb M i j b _ _ (hWc i j 1 a b)).1)
      (etale := by
        intro i j a b
        exact MorphismProperty.of_isPullback (P := @Etale) (hpb i j a b).flip
          (hOne p D G L R gb M i j b _ _ (hWc i j 1 a b)).2.1)
      (onto := by
        intro i j a b
        exact MorphismProperty.of_isPullback (P := @Surjective) (hpb i j a b).flip
          (hOne p D G L R gb M i j b _ _ (hWc i j 1 a b)).2.2)
      (trans := by
        intro i j a b hnorm Ω _ _ x y hxy
        have hbase : (x ≫ (GlobalTheory.KS.pow (M i).univ.A k).hom) ≫ πc i j 1 a b = (y ≫ (GlobalTheory.KS.pow (M i).univ.A k).hom) ≫ πc i j 1 a b := by
          have := congrArg (· ≫ (GlobalTheory.KS.pow (M j).univ.A k).hom) hxy
          simp only [Category.assoc, GlobalTheory.KS.PowPB.powMap_w] at this
          simpa only [Category.assoc] using this
        obtain ⟨u, hu, hall⟩ := hTr p D G L R gb M i j (πc i j 1 a b) (Φc i j 1 a b) (hWc i j 1 a b) Ω _ _ hbase
        refine ⟨u, hu, hint hu, hnorm u hu, ?_⟩
        obtain ⟨h1, h2⟩ := hall _ _ (hWc i i u (hint hu) (hnorm u hu))
        exact powMap_ext' _ _ _ _ _ _ k (hpb i j a b) x y hxy h1 h2)
      (free := by
        intro i j hij u hu a b Ω _ _ x hx
        refine hFree p D G L R gb M i j hij u hu (πc i i u a b) (Φc i i u a b) (hWc i i u a b) Ω
          (x ≫ (GlobalTheory.KS.pow (M i).univ.A k).hom) ?_
        have := congrArg (· ≫ (GlobalTheory.KS.pow (M i).univ.A k).hom) hx
        simpa only [Category.assoc, GlobalTheory.KS.PowPB.powMap_w] using this)
  refine ⟨⟨T, Equiv.refl _, fun N => rfl, fun h => Iff.rfl, M, fun N => Iso.refl _, fun N => Category.id_comp _, ?_⟩⟩
  intro N' N h a b
  have hc := comp_univ_hom_eq_of_wit (hWc N' N h a b)
  obtain ⟨hs, o, ψ, φ, ht, hΦ⟩ := hWc N' N h a b
  refine ⟨πc N' N h a b, o, ψ, φ, hΦ ▸ hc, hs, ht, ?_⟩
  exact (Category.comp_id _).trans ((powMap_congr' rfl hΦ hc (hΦ ▸ hc) k).trans (Category.id_comp _).symm)
