import Development.EtaleCohomology.EtaleSheaves.FibStalkPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.FibPf LateralTheory.E.FibClosedPf LateralTheory.E.FibStalkPf

namespace LateralTheory.E.FibreEqvPf

theorem eqv_snd_snd {q : ℕ} {i : ℤ} {Z S K L : Scheme.{0}} (c : Z ⟶ S) (t : L ⟶ S) (k : K ⟶ L) :
    Eqv _ (sch.map (pullback.snd (pullback.snd c t) k)) (tw q i) ↔ Eqv _ (sch.map (pullback.snd c (k ≫ t))) (tw q i) := by
  have e := pullbackLeftPullbackSndIso_hom_snd c t k
  rw [← e, Functor.map_comp]
  exact ⟨fun h => eqv_right h (eqv_iso (pullbackLeftPullbackSndIso c t k) q i), fun h => eqv_comp (eqv_iso _ q i) h⟩

theorem eqv_snd_iso {q : ℕ} {i : ℤ} {Z S K K' : Scheme.{0}} (c : Z ⟶ S) (T : K ⟶ S) (ρ : K' ⟶ K) [IsIso ρ]
    (h : Eqv _ (sch.map (pullback.snd c T)) (tw q i)) : Eqv _ (sch.map (pullback.snd c (ρ ≫ T))) (tw q i) := by
  rw [← eqv_snd_snd]
  have w : sch.map (pullback.snd (pullback.snd c T) ρ) ≫ sch.map ρ = sch.map (pullback.fst (pullback.snd c T) ρ) ≫ sch.map (pullback.snd c T) := by
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  refine eqv_left (g := sch.map ρ) ?_ (eqv_iso (asIso ρ) q i)
  rw [w]
  exact eqv_comp (eqv_iso (asIso (pullback.fst (pullback.snd c T) ρ)) q i) h

def StalkFib : Prop := Hyp → HZero → AICAcyc → ∀ (q : ℕ) (i : ℤ) {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c]
  [QuasiSeparated c] [IsDominant c], AICSch Z → AICSch S → ∀ x : S, IsUnit (q : S.presheaf.stalk x) →
  Eqv _ (sch.map (pullback.snd c (S.fromSpecStalk x))) (tw q i)

theorem residue_bij {R R' : Type} [CommRing R] [CommRing R'] [IsLocalRing R] [IsLocalRing R'] (f : R →+* R') [IsLocalHom f]
    (hf : Function.Surjective f) : Function.Bijective (IsLocalRing.ResidueField.map f) := by
  refine ⟨(IsLocalRing.ResidueField.map f).injective, fun y => ?_⟩
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨IsLocalRing.residue R x, IsLocalRing.ResidueField.map_residue f x⟩

theorem geom (H : Hyp) (h0 : HZero) (hA : AICAcyc) (hS : StalkSHS) (hF : StalkFib) (q : ℕ) (i : ℤ) {Z S : Scheme.{0}}
    (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c] (hZs : AICSch Z) (hSs : AICSch S)
    (hB : ∀ (B : Type) [CommRing B] [IsLocalRing B], SH B → IsUnit (q : B) → ∀ t : Spec (CommRingCat.of B) ⟶ S, PB q i (pullback.snd c t))
    (x : S) (hu : IsUnit (q : S.presheaf.stalk x)) :
    Eqv _ (sch.map (pullback.snd c (cpt (S.presheaf.stalk x) ≫ S.fromSpecStalk x))) (tw q i) := by
  have hsh := hS S hSs x
  obtain ⟨_, _⟩ := id hsh
  have hx := hF H h0 hA q i c hZs hSs x hu
  have hpb : Eqv _ (sch.map (pullback.fst (pullback.snd c (S.fromSpecStalk x)) (cpt (S.presheaf.stalk x)))) (tw q i) :=
    hB _ hsh hu (S.fromSpecStalk x)
  have hE1 : Eqv _ (sch.map (cpt (S.presheaf.stalk x))) (tw q i) := H.e1 q _ (IsLocalRing.maximalIdeal _) hu i
  rw [← eqv_snd_snd]
  refine eqv_left (g := sch.map (cpt (S.presheaf.stalk x))) ?_ hE1
  rw [← Functor.map_comp, ← pullback.condition, Functor.map_comp]
  exact eqv_comp hpb hx

theorem FibreEqv_of (hS : StalkSHS) (hF : StalkFib) : FibreEqv := by
  intro H h0 hA q i A _ _ hq Z S c p _ _ _ _ _ hZs hSs hB s
  set j := pullback.fst p (cpt A)
  have h1 : SurjectiveOnStalks (cpt A) :=
    SurjectiveOnStalks.Spec_iff.2 (RingHom.surjectiveOnStalks_of_surjective IsLocalRing.residue_surjective)
  have h2 : SurjectiveOnStalks j := MorphismProperty.of_isPullback (P := @SurjectiveOnStalks) (IsPullback.of_hasPullback p (cpt A)).flip h1
  have hsurj : Function.Surjective (j.stalkMap s).hom := j.stalkMap_surjective s
  have hu0 : IsUnit (q : Γ(S, ⊤)) := unit_of hq p
  have hu : IsUnit (q : S.presheaf.stalk (j s)) := by
    simpa using hu0.map (S.presheaf.germ ⊤ (j s) trivial).hom
  have hbij := residue_bij (j.stalkMap s).hom hsurj
  let ρ : Spec (CommRingCat.of (IsLocalRing.ResidueField ((pullback p (cpt A)).presheaf.stalk s))) ⟶
      Spec (CommRingCat.of (IsLocalRing.ResidueField (S.presheaf.stalk (j s)))) :=
    Spec.map (RingEquiv.ofBijective _ hbij).toCommRingCatIso.hom
  have sq : cpt ((pullback p (cpt A)).presheaf.stalk s) ≫ (pullback p (cpt A)).fromSpecStalk s ≫ j =
      ρ ≫ cpt (S.presheaf.stalk (j s)) ≫ S.fromSpecStalk (j s) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk j, ← Category.assoc, ← Category.assoc]
    congr 1
    simp only [ρ, cpt, ← Spec.map_comp]
    congr 1
  rw [eqv_snd_snd, sq]
  exact eqv_snd_iso c _ ρ (geom H h0 hA hS hF q i c hZs hSs hB (j s) hu)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def BaseAIC : Prop := ∀ {Z S : Scheme.{0}} (c : Z ⟶ S) [QuasiCompact c] [QuasiSeparated c] [IsDominant c],
  AICSch Z → AICSch S → ∀ x : S, AICSch (pullback c (S.fromSpecStalk x))

def StalkAIC : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AICSch (Spec (S.presheaf.stalk x))

theorem StalkFib_of (hZB : BaseAIC) (hSA : StalkAIC) : StalkFib := by
  intro H h0 hA q i Z S c _ _ _ hZs hSs x hu
  have hB := hZB c hZs hSs x
  have hK := hSA S hSs x
  have : IsIntegral (pullback c (S.fromSpecStalk x) : Scheme.{0}) := hB.1
  have : ConnectedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) := inferInstance
  have : CompactSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd c (S.fromSpecStalk x))
  have : QuasiSeparatedSpace (pullback c (S.fromSpecStalk x) : Scheme.{0}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd c (S.fromSpecStalk x))
  have hu1 : IsUnit (q : Γ(Spec (S.presheaf.stalk x), ⊤)) := unit_of (A := S.presheaf.stalk x) hu (𝟙 _)
  have hu2 : IsUnit (q : Γ(pullback c (S.fromSpecStalk x), ⊤)) :=
    unit_of (A := S.presheaf.stalk x) hu (pullback.snd c (S.fromSpecStalk x))
  exact eqv_of H.a9 _ (h0 H q (pullback.snd c (S.fromSpecStalk x)) hK inferInstance hu1 i) (fun n hn => hA H q _ hB hu2 n i hn)
    (fun n hn => hA H q _ hK hu1 n i hn)

end LateralTheory.E.FibreEqvPf

namespace LateralTheory.E.FibreEqvPf

def StalkAICRing : Prop := ∀ (S : Scheme.{0}), AICSch S → ∀ x : S, AIC (S.presheaf.stalk x)

def SpecAIC : Prop := ∀ (B : CommRingCat.{0}), IsDomain B → AIC B → AICSch (Spec B)

theorem StalkAIC_of (h1 : StalkAICRing) (h2 : SpecAIC) : StalkAIC := by
  intro S hS x
  have : IsIntegral S := hS.1
  exact h2 _ inferInstance (h1 S hS x)

end LateralTheory.E.FibreEqvPf
