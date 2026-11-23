import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

theorem prd_sub_C_mem {σ R : Type} [CommRing R] (p : MvPolynomial σ R) :
    p - MvPolynomial.C (MvPolynomial.constantCoeff p) ∈
      Ideal.span (Set.range (MvPolynomial.X : σ → MvPolynomial σ R)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr =>
    have e : p + r - MvPolynomial.C (MvPolynomial.constantCoeff (p + r)) =
        (p - MvPolynomial.C (MvPolynomial.constantCoeff p)) + (r - MvPolynomial.C (MvPolynomial.constantCoeff r)) := by
      simp only [map_add]; ring
    rw [e]; exact Ideal.add_mem _ hp hr
  | mul_X p i _ =>
    have e : p * MvPolynomial.X i - MvPolynomial.C (MvPolynomial.constantCoeff (p * MvPolynomial.X i)) =
        p * MvPolynomial.X i := by simp
    rw [e]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem prd_nbhd_psi {d : ℕ} {A B : Type} [CommRing A] [CommRing B] (I : Ideal A) (φ : A →+* B)
    (ψ : MvPolynomial (Fin d) (A ⧸ I) →+* B) (hφ : Nbhd φ I) (hψ : ψ.Etale)
    (hIB : I.map φ = Ideal.span (Set.range fun j => ψ (MvPolynomial.X j)))
    (hl : ∀ a : A, φ a - ψ (MvPolynomial.C (Ideal.Quotient.mk I a)) ∈ I.map φ) :
    Nbhd ψ (Ideal.span (Set.range MvPolynomial.X)) := by
  refine ⟨hψ, ?_⟩
  have hQ : (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ = I.map φ := by
    rw [Ideal.map_span, hIB, ← Set.range_comp]; rfl
  have key : ∀ a : A, ψ (MvPolynomial.C (Ideal.Quotient.mk I a)) - φ a ∈
      (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ := by
    intro a; rw [hQ, ← neg_sub]; exact (Ideal.neg_mem_iff _).2 (hl a)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (MvPolynomial.constantCoeff p)
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    have h1 := prd_sub_C_mem p
    have h2 : ψ p - ψ (MvPolynomial.C (MvPolynomial.constantCoeff p)) ∈
        (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ := by
      rw [← map_sub]; exact Ideal.mem_map_of_mem _ h1
    have h3 : φ a ∈ I.map φ := by
      rw [← hQ]
      have h5 := Ideal.sub_mem _ hx h2
      rw [sub_sub_cancel, ← ha] at h5
      have h6 := Ideal.sub_mem _ h5 (key a)
      rwa [sub_sub_cancel] at h6
    have h4 : Ideal.Quotient.mk I a = 0 := by
      apply hφ.2.1
      rw [map_zero, Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem]; exact h3
    rw [Ideal.Quotient.eq_zero_iff_mem]
    rw [← ha, h4, map_zero, sub_zero] at h1
    exact h1
  · intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hφ.2.2 (Ideal.Quotient.mk (I.map φ) b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hx
    refine ⟨Ideal.Quotient.mk _ (MvPolynomial.C (Ideal.Quotient.mk I a)), ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    have hx' : φ a - b ∈ (Ideal.span (Set.range (MvPolynomial.X : Fin d → MvPolynomial (Fin d) (A ⧸ I)))).map ψ := by
      rw [hQ]; exact hx
    have h7 := Ideal.add_mem _ (key a) hx'
    rwa [sub_add_sub_cancel] at h7

theorem prd_indNbhd_of_nbhd {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A) (h : Nbhd φ I) :
    IndNbhd φ I := by
  refine ⟨Discrete PUnit, inferInstance, inferInstance, (Functor.const _).obj (CommRingCat.of B),
    { app := fun _ => CommRingCat.ofHom φ, naturality := fun _ _ _ => by simp }, 𝟙 _, ⟨?_⟩, fun _ => ⟨h, ?_⟩⟩
  · exact { desc := fun s => s.ι.app ⟨⟨⟩⟩
            fac := fun s j => by rcases j with ⟨⟨⟩⟩; simp
            uniq := fun s m hm => by simpa using hm ⟨⟨⟩⟩ }
  · simp

theorem prd_off_le {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hJ : J ≤ I.map f) : off B J ≤ Spec.map (CommRingCat.ofHom f) ⁻¹ᵁ off A I := by
  intro x hx h'
  apply hx
  change (J : Set B) ⊆ x.asIdeal
  have h'' : (I : Set A) ⊆ (Ideal.comap f x.asIdeal) := h'
  exact hJ.trans (Ideal.map_le_iff_le_comap.2 h'')

theorem prd_opnMap_comp {X'' X' X : Scheme.{0}} (f : X'' ⟶ X') (g : X' ⟶ X) (U'' : X''.Opens) (U' : X'.Opens)
    (U : X.Opens) (h : U'' ≤ f ⁻¹ᵁ U') (h' : U' ≤ g ⁻¹ᵁ U) (h'' : U'' ≤ (f ≫ g) ⁻¹ᵁ U) :
    opnMap f U'' U' h ≫ opnMap g U' U h' = opnMap (f ≫ g) U'' U h'' := by
  apply Arrow.hom_ext
  · change sch.map _ ≫ sch.map _ = sch.map _
    rw [← Functor.map_comp, Scheme.Hom.resLE_comp_resLE]
  · change sch.map f ≫ sch.map g = sch.map (f ≫ g)
    rw [Functor.map_comp]

theorem prd_opnMap_congr {X' X : Scheme.{0}} {f f' : X' ⟶ X} (e : f = f') (U' : X'.Opens) (U : X.Opens)
    (h : U' ≤ f ⁻¹ᵁ U) (h' : U' ≤ f' ⁻¹ᵁ U) : opnMap f U' U h = opnMap f' U' U h' := by
  subst e; rfl

theorem prd_exc_left (q : ℕ) {P'' P' P : Arrow Spc} {φ : P'' ⟶ P'} {ψ : P' ⟶ P} (h : Exc q (φ ≫ ψ))
    (h' : Exc q ψ) : Exc q φ := fun n i => by
  have e : ⇑(Hs.pull q (φ ≫ ψ) n i) = Hs.pull q φ n i ∘ Hs.pull q ψ n i := funext (hs_pull_comp q φ ψ n i)
  have h2 := h n i
  rw [e] at h2
  exact (Function.Bijective.of_comp_iff _ (h' n i)).1 h2

theorem prd_spMap_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  change sch.map _ ≫ sch.map _ = sch.map _
  rw [← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem prd_pull_bij {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (hg : Function.Bijective g) (q : ℕ)
    (i n : ℤ) : Function.Bijective (pull _ (spMap g) (tw q i) n) := by
  let e := RingEquiv.ofBijective g hg
  have hid : ∀ (T : Type) [CommRing T], spMap (RingHom.id T) = 𝟙 _ := fun T _ => by
    change sch.map _ = _
    rw [CommRingCat.ofHom_id, Spec.map_id, CategoryTheory.Functor.map_id]
  have h1 : spMap g ≫ spMap (e.symm : S →+* R) = 𝟙 _ := by
    rw [prd_spMap_comp]
    have : g.comp (e.symm : S →+* R) = RingHom.id S := by ext x; exact e.apply_symm_apply x
    rw [this, hid]
  have h2 : spMap (e.symm : S →+* R) ≫ spMap g = 𝟙 _ := by
    rw [prd_spMap_comp]
    have : (e.symm : S →+* R).comp g = RingHom.id R := by ext x; exact e.symm_apply_apply x
    rw [this, hid]
  refine Function.bijective_iff_has_inverse.2 ⟨pull _ (spMap (e.symm : S →+* R)) (tw q i) n, fun x => ?_, fun x => ?_⟩
  · rw [← pull_comp, h2, pull_id]
  · rw [← pull_comp, h1, pull_id]

theorem prd_le_comp {X'' X' X : Scheme.{0}} {f : X'' ⟶ X'} {g : X' ⟶ X} {U'' : X''.Opens} {U' : X'.Opens}
    {U : X.Opens} (h : U'' ≤ f ⁻¹ᵁ U') (h' : U' ≤ g ⁻¹ᵁ U) : U'' ≤ (f ≫ g) ⁻¹ᵁ U := by
  intro x hx
  have h2 := h' (h hx)
  simpa using h2

theorem prd_transfer (hAN : LeafActNat) (a6 : DivisorNaturality) {d q : ℕ} [NeZero q] {A' C : Type} [CommRing A'] [CommRing C]
    (IA : Ideal A') (K : Ideal C) (m : A' →+* C) (hm : off C K ≤ Spec.map (CommRingCat.ofHom m) ⁻¹ᵁ off A' IA)
    (cA : Hs q (opn (off A' IA)) (2 * d) d) (cC : Hs q (opn (off C K)) (2 * d) d)
    (hcl : Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom m)) (off C K) (off A' IA) hm) _ _ cA = cC)
    (hexc : Exc q (opnMap (Spec.map (CommRingCat.ofHom m)) (off C K) (off A' IA) hm))
    (hpull : ∀ n i : ℤ, Function.Bijective (pull _ (spMap m) (tw q i) n))
    (hC : ∀ n i : ℤ, Function.Bijective fun b : Ht q (sp C) n i => Hs.act q (P := opn (off C K)) b cC)
    (n i : ℤ) : Function.Bijective fun a : Ht q (sp A') n i => Hs.act q (P := opn (off A' IA)) a cA := by
  refine (Function.Bijective.of_comp_iff' (hexc _ _) _).1 ?_
  have e : (⇑(Hs.pull q (opnMap (Spec.map (CommRingCat.ofHom m)) (off C K) (off A' IA) hm) (n + 2 * d) (i + d)) ∘
      fun a : Ht q (sp A') n i => Hs.act q (P := opn (off A' IA)) a cA) =
      (fun b : Ht q (sp C) n i => Hs.act q (P := opn (off C K)) b cC) ∘ ⇑(pull _ (spMap m) (tw q i) n) := by
    funext a
    simp only [Function.comp]
    have e2 := hAN a6 q _ _ (opnMap (Spec.map (CommRingCat.ofHom m)) (off C K) (off A' IA) hm) n (2 * d) i d a cA
    rw [hcl] at e2
    exact e2
  rw [e]; exact (hC n i).comp (hpull n i)

theorem LeafPrdRing_of (hQ : LeafQuot) (hIE : LeafIndExc) (hT : LeafThom) (hPA : LeafPrdAff) (hAN : LeafActNat) :
    LeafPrdRing := by
  intro hyp H d q _ A _ I hq hI hch c hc h n i
  have hyp' := hyp
  obtain ⟨a1, -, -, a4, a6, -, -, -, b1, -, -, e1⟩ := hyp'
  obtain ⟨B, _, φ, ψ, hφ, hψ, hIB, hl⟩ := hch
  obtain ⟨th, hth⟩ := hT hyp d
  have hTh : IsThom d (thom d) := @pick_spec _ ⟨fun _ _ _ _ _ _ => 0⟩ _ ⟨th, hth⟩
  have hqB : IsUnit (q : B) := by simpa using hq.map φ
  have hqR : IsUnit (q : A ⧸ I) := by simpa using hq.map (Ideal.Quotient.mk I)
  have hqA' : IsUnit (q : H.obj A I) := by simpa using hq.map (H.η A I)
  have hqC : IsUnit (q : H.obj B (I.map φ)) := by simpa using hqB.map (H.η B (I.map φ))
  obtain ⟨m, hmdef⟩ : ∃ m, m = H.map (I := I) (J := I.map φ) φ Ideal.le_comap_map := ⟨_, rfl⟩
  have hmη : m.comp (H.η A I) = (H.η B (I.map φ)).comp φ := by rw [hmdef]; exact H.map_η _ _
  have hK' : (I.map φ).map (H.η B (I.map φ)) = (I.map (H.η A I)).map m := by
    rw [Ideal.map_map, Ideal.map_map, hmη]
  have hy : Ideal.span (Set.range fun j => H.η B (I.map φ) (ψ (MvPolynomial.X j))) =
      (I.map φ).map (H.η B (I.map φ)) := by
    have e := congrArg (Ideal.map (H.η B (I.map φ))) hIB
    rw [e, Ideal.map_span, ← Set.range_comp]; rfl
  have hm : off _ ((I.map φ).map (H.η B (I.map φ))) ≤ Spec.map (CommRingCat.ofHom m) ⁻¹ᵁ off _ (I.map (H.η A I)) :=
    prd_off_le _ _ _ (le_of_eq hK')
  have hB : off _ ((I.map φ).map (H.η B (I.map φ))) ≤
      Spec.map (CommRingCat.ofHom (H.η B (I.map φ))) ⁻¹ᵁ off B (I.map φ) := prd_off_le _ _ _ le_rfl
  have hφo : off B (I.map φ) ≤ Spec.map (CommRingCat.ofHom φ) ⁻¹ᵁ off A I := prd_off_le _ _ _ le_rfl
  have excA := hIE a1 a4 b1 q (H.η A I) I hI (H.ind A I) hq h
  have excB := hIE a1 a4 b1 q (H.η B (I.map φ)) (I.map φ) (hI.map φ) (H.ind B _) hqB hB
  have excφ := hIE a1 a4 b1 q φ I hI (prd_indNbhd_of_nbhd φ I hφ) hq hφo
  have hSpec : Spec.map (CommRingCat.ofHom m) ≫ Spec.map (CommRingCat.ofHom (H.η A I)) =
      Spec.map (CommRingCat.ofHom (H.η B (I.map φ))) ≫ Spec.map (CommRingCat.ofHom φ) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hmη]
  have hΦG : opnMap _ _ _ hm ≫ opnMap _ _ _ h = opnMap _ _ _ hB ≫ opnMap _ _ _ hφo := by
    rw [prd_opnMap_comp _ _ _ _ _ hm h (prd_le_comp hm h), prd_opnMap_comp _ _ _ _ _ hB hφo (prd_le_comp hB hφo)]
    exact prd_opnMap_congr hSpec _ _ _ _
  have excΦ : Exc q (opnMap _ _ _ hm) := by
    refine prd_exc_left q ?_ excA
    rw [hΦG]; exact exc_comp q excB excφ
  have hcl : Hs.pull q (opnMap _ _ _ hm) _ _ (Hs.pull q (opnMap _ _ _ h) _ _ c) =
      thom d q (H.obj B (I.map φ)) ((I.map φ).map (H.η B (I.map φ))) _ hy := by
    rw [← hs_pull_comp, hΦG, hs_pull_comp, hc B φ (fun j => ψ (MvPolynomial.X j)) hIB.symm hφo hφ.1]
    exact (hTh q).1 B (H.obj B (I.map φ)) (H.η B (I.map φ)) (I.map φ) _ (fun j => ψ (MvPolynomial.X j)) hIB.symm hy hB hqB
  have hpull : ∀ n i : ℤ, Function.Bijective (pull _ (spMap m) (tw q i) n) := by
    intro n i
    have := H.hens A I
    have := H.hens B (I.map φ)
    have eA := e1 q (H.obj A I) (I.map (H.η A I)) hqA' i n
    have eC := e1 q (H.obj B (I.map φ)) ((I.map φ).map (H.η B (I.map φ))) hqC i n
    have hle : I.map (H.η A I) ≤ ((I.map φ).map (H.η B (I.map φ))).comap m := by
      rw [hK']; exact Ideal.le_comap_map
    have hqm : Function.Bijective (Ideal.quotientMap _ m hle) := by
      have hqA := hQ A (H.obj A I) (H.η A I) I (H.ind A I)
      have hqB' := hQ B (H.obj B (I.map φ)) (H.η B (I.map φ)) (I.map φ) (H.ind _ _)
      have hcomp : ⇑(Ideal.quotientMap _ m hle) ∘ ⇑(Ideal.quotientMap (I.map (H.η A I)) (H.η A I) Ideal.le_comap_map) =
          ⇑(Ideal.quotientMap ((I.map φ).map (H.η B (I.map φ))) (H.η B (I.map φ)) Ideal.le_comap_map) ∘
          ⇑(Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) := by
        funext x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        simp only [Function.comp, Ideal.quotientMap_mk]
        rw [show m (H.η A I a) = H.η B (I.map φ) (φ a) from RingHom.congr_fun hmη a]
      exact (Function.Bijective.of_comp_iff _ hqA).1 (by rw [hcomp]; exact hqB'.comp hφ.2)
    have hsq : spMap (Ideal.Quotient.mk ((I.map φ).map (H.η B (I.map φ)))) ≫ spMap m =
        spMap (Ideal.quotientMap _ m hle) ≫ spMap (Ideal.Quotient.mk (I.map (H.η A I))) := by
      rw [prd_spMap_comp, prd_spMap_comp, Ideal.quotientMap_comp_mk]
    have e : ⇑(pull _ (spMap (Ideal.Quotient.mk ((I.map φ).map (H.η B (I.map φ))))) (tw q i) n) ∘
        ⇑(pull _ (spMap m) (tw q i) n) = ⇑(pull _ (spMap (Ideal.quotientMap _ m hle)) (tw q i) n) ∘
        ⇑(pull _ (spMap (Ideal.Quotient.mk (I.map (H.η A I)))) (tw q i) n) := by
      funext x
      simp only [Function.comp]
      rw [← pull_comp, ← pull_comp, hsq]
    exact (Function.Bijective.of_comp_iff' eC _).1 (by rw [e]; exact (prd_pull_bij _ hqm q i n).comp eA)
  have hC := fun n i => hPA hyp d q (A ⧸ I) B (H.obj B (I.map φ)) ψ (H.η B (I.map φ)) hqR
    (prd_nbhd_psi I φ ψ hφ hψ hIB hl) (I.map φ) _ (H.ind B _) rfl (H.hens B _) hIB.symm hy n i
  exact prd_transfer hAN a6 (I.map (H.η A I)) _ m hm _ _ hcl excΦ hpull hC n i

end LateralTheory.CohomologicalPurity.TubeCut
