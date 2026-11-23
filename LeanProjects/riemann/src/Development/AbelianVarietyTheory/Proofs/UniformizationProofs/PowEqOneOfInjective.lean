import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExpansionBijectiveOverFields
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PowEqOneOfPush
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ThetaGrpActsLinearly
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFOfIntegral

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ThetaSpecialise

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
  GlobalTheory.ThetaBaseChange

section Pull

variable {X X' X'' Y Y' Y'' Y₁ Y₁' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {Φ : X' ⟶ X} {Φ' : X'' ⟶ X'}
  {K : Type} [Fintype K] {ε : K → ℤ}

def IsPull {φ₁ : K → (Y₁ ⟶ X)} {φ : K → (Y ⟶ X)} (a : Y₁ ⟶ Y) (t : LB.Sec (LB.LinComb L φ₁ ε))
    (s : LB.Sec (LB.LinComb L φ ε)) : Prop :=
  (∀ κ, φ₁ κ = a ≫ φ κ) ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁) (z : Z) (j : K → L.ι), (∀ κ, φ₁ κ (r z) ∈ L.U (j κ)) →
    gs r z (LB.wchart L φ₁ j) (t.f j) = gs (r ≫ a) z (LB.wchart L φ j) (s.f j)

theorem isPull_pullOver {R R' : Type} [CommRing R] [CommRing R'] {φ : K → (Y ⟶ X)}
    {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) {φ' : K → (Y' ⟶ X)}
    (hφ : ∀ k, φ' k = p ≫ φ k) (s : SecOver π (LB.LinComb L φ ε)) : IsPull p (pullOver L ε hp hφ s) s := by
  unfold IsPull
  exact ⟨hφ, fun _ r z j hj => gs_pullOver hp hφ s r z j hj⟩

variable {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X)} {φ₂ : K → (Y₁' ⟶ X)} {a : Y₁ ⟶ Y} {b : Y₁' ⟶ Y₁}
  {s : LB.Sec (LB.LinComb L φ ε)} {t : LB.Sec (LB.LinComb L φ₁ ε)} {v : LB.Sec (LB.LinComb L φ₂ ε)}

theorem IsPull.comp (h₁ : IsPull b v t) (h₂ : IsPull a t s) {c : Y₁' ⟶ Y} (hc : b ≫ a = c) : IsPull c v s := by
  unfold IsPull at h₁ h₂ ⊢
  obtain ⟨h₁φ, h₁g⟩ := h₁
  obtain ⟨h₂φ, h₂g⟩ := h₂
  subst hc
  refine ⟨fun κ => by rw [h₁φ κ, h₂φ κ, Category.assoc], fun Z r z j hj => ?_⟩
  rw [h₁g Z r z j hj, h₂g Z (r ≫ b) z j ?_, Category.assoc]
  intro κ
  have hκ := hj κ
  rw [h₁φ κ, Scheme.Hom.comp_apply] at hκ
  rwa [Scheme.Hom.comp_apply]

theorem IsPull.sval (h : IsPull a t s) {Z : Scheme.{0}} (r : Z ⟶ Y₁) {z : Z} {J} (hJ : Good L z J) :
    sval t r z J = sval s (r ≫ a) z J := by
  unfold IsPull at h
  have hmem : ∀ k, φ₁ k (r z) ∈ L.U (J (r ≫ φ₁ k)) := fun k => by
    simpa only [Scheme.Hom.comp_apply] using hJ (r ≫ φ₁ k)
  rw [sval_of t r z J (fun k => J (r ≫ φ₁ k)) (fun _ => rfl), h.2 Z r z _ hmem]
  exact (sval_of s (r ≫ a) z J _ (fun k => by rw [h.1 k, Category.assoc])).symm

theorem secScal_one_iff (hL : L.IsLB) : GeneratorPullback.SecScal L φ₁ ε t φ ε s a 1 ↔
    ∀ y J, Good L y J → Geo.Tor.sval s (𝟙 Y₁ ≫ a) y J = Geo.Tor.sval t (𝟙 Y₁) y J := by
  have h1 : ∀ y : Y₁, gs (𝟙 Y₁) y ⊤ (1 : Γ(Y₁, ⊤)) = 1 := fun y => by
    rw [gs_eq _ _ _ (by simp), map_one, map_one]
  simp only [secScal_iff_val hL, h1, _root_.one_mul]

theorem eq_pullOver_of_secScal (hL : L.IsLB) {R R' : Type} [CommRing R] [CommRing R']
    {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y₁ ⟶ Spec (CommRingCat.of R')}
    {f : R →+* R'} (hp : a ≫ π = π' ≫ Spec.map (CommRingCat.ofHom f)) (hφ : ∀ k, φ₁ k = a ≫ φ k)
    (h : GeneratorPullback.SecScal L φ₁ ε t φ ε s a 1) : pullOver L ε hp hφ s = t := by
  apply sec_ext' hL
  intro y J hJ
  rw [sval_pullOver hp hφ s (𝟙 Y₁) hJ]
  exact (secScal_one_iff hL).1 h y J hJ

variable {w : LB.Iso L' (L.pull Φ)} {φ' : K → (Y' ⟶ X')} {s' : LB.Sec (LB.LinComb L' φ' ε)}

theorem psec_iff_of_isPull {h₁ : Y' ⟶ Y₁} (hc : ∀ κ, φ' κ ≫ Φ = h₁ ≫ φ₁ κ) (H : IsPull a t s) {h : Y' ⟶ Y}
    (e : h₁ ≫ a = h) : PSec w φ' φ₁ ε h₁ s' t ↔ PSec w φ' φ ε h s' s := by
  unfold IsPull at H
  subst e
  unfold PSec
  refine forall_congr' fun Z => forall_congr' fun r => forall_congr' fun z => forall_congr' fun p =>
    forall_congr' fun q => imp_congr_right fun hp => imp_congr_right fun _ => ?_
  have hmem : ∀ κ, φ₁ κ ((r ≫ h₁) z) ∈ L.U (p κ) := fun κ => by
    have hκ := congrArg (fun g : Y' ⟶ X => g (r z)) (hc κ)
    simp only [Scheme.Hom.comp_apply] at hκ
    rw [Scheme.Hom.comp_apply, ← hκ]
    exact hp κ
  rw [H.2 Z (r ≫ h₁) z p hmem, Category.assoc]

theorem PSec.pull_left {h : Y' ⟶ Y} (H : PSec w φ' φ ε h s' s) {φ₁' : K → (Y₁' ⟶ X')} {a' : Y₁' ⟶ Y'}
    {t' : LB.Sec (LB.LinComb L' φ₁' ε)} (H' : IsPull a' t' s') : PSec w φ₁' φ ε (a' ≫ h) t' s := by
  unfold IsPull at H'
  unfold PSec at H ⊢
  intro Z r z p q hp hq
  have hp' : ∀ κ, Φ (φ' κ ((r ≫ a') z)) ∈ L.U (p κ) := fun κ => by
    have hκ := hp κ
    rw [H'.1 κ, Scheme.Hom.comp_apply] at hκ
    rwa [Scheme.Hom.comp_apply]
  have hq' : ∀ κ, φ' κ ((r ≫ a') z) ∈ L'.U (q κ) := fun κ => by
    have hκ := hq κ
    rw [H'.1 κ, Scheme.Hom.comp_apply] at hκ
    rwa [Scheme.Hom.comp_apply]
  have e : ∀ κ, r ≫ φ₁' κ = (r ≫ a') ≫ φ' κ := fun κ => by rw [H'.1 κ, Category.assoc]
  have key := H Z (r ≫ a') z p q hp' hq'
  rw [Category.assoc] at key
  rw [H'.2 Z r z q hq, key]
  simp only [e]

theorem PSec.cancel {w' : LB.Iso L'' (L'.pull Φ')} {w'' : LB.Iso L'' (L.pull (Φ' ≫ Φ))} (T : Tri w w' w'')
    (hL : L.IsLB) {φ'' : K → (Y'' ⟶ X'')} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} (hc : ∀ k, φ'' k ≫ Φ' = h' ≫ φ' k)
    {s'' : LB.Sec (LB.LinComb L'' φ'' ε)} (H : PSec w φ' φ ε h s' s) (H'' : PSec w'' φ'' φ ε (h' ≫ h) s'' s) :
    PSec w' φ'' φ' ε h' s'' s' := by
  unfold Tri at T
  unfold PSec at H H'' ⊢
  intro Z r z p q hp hq
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
  set P : K → L.ι := fun κ => J (r ≫ φ'' κ ≫ Φ' ≫ Φ)
  have hPmem : ∀ κ, Φ (Φ' (φ'' κ (r z))) ∈ L.U (P κ) := fun κ => by
    simpa only [Scheme.Hom.comp_apply] using hJ (r ≫ φ'' κ ≫ Φ' ≫ Φ)
  have pt : ∀ κ, φ' κ (h' (r z)) = Φ' (φ'' κ (r z)) := fun κ => by
    have hκ := congrArg (fun g : Y'' ⟶ X' => g (r z)) (hc κ)
    simp only [Scheme.Hom.comp_apply] at hκ
    exact hκ.symm
  have hP' : ∀ κ, Φ (φ' κ ((r ≫ h') z)) ∈ L.U (P κ) := fun κ => by
    rw [Scheme.Hom.comp_apply, pt κ]; exact hPmem κ
  have hp' : ∀ κ, φ' κ ((r ≫ h') z) ∈ L'.U (p κ) := fun κ => by
    rw [Scheme.Hom.comp_apply, pt κ]; exact hp κ
  have hP'' : ∀ κ, (Φ' ≫ Φ) (φ'' κ (r z)) ∈ L.U (P κ) := fun κ => by
    rw [Scheme.Hom.comp_apply]; exact hPmem κ
  have e : ∀ κ, (r ≫ φ'' κ) ≫ Φ' = (r ≫ h') ≫ φ' κ := fun κ => by
    rw [Category.assoc, hc κ, Category.assoc]
  have hprod : (∏ κ, gw w'' (r ≫ φ'' κ) z (P κ) (q κ) ^ ε κ) =
      (∏ κ, gw w ((r ≫ h') ≫ φ' κ) z (P κ) (p κ) ^ ε κ) * ∏ κ, gw w' (r ≫ φ'' κ) z (p κ) (q κ) ^ ε κ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun κ _ => ?_
    have m1 : Φ (Φ' ((r ≫ φ'' κ) z)) ∈ L.U (P κ) := by rw [Scheme.Hom.comp_apply]; exact hPmem κ
    have m2 : Φ' ((r ≫ φ'' κ) z) ∈ L'.U (p κ) := by rw [Scheme.Hom.comp_apply]; exact hp κ
    have m3 : (r ≫ φ'' κ) z ∈ L''.U (q κ) := by rw [Scheme.Hom.comp_apply]; exact hq κ
    rw [← mul_zpow, T Z (r ≫ φ'' κ) z (P κ) (p κ) (q κ) m1 m2 m3, e κ]
  have k1 := H Z (r ≫ h') z P p hP' hp'
  have k2 := H'' Z r z P q hP'' hq
  rw [Category.assoc] at k1
  rw [k1, hprod, Units.val_mul, _root_.mul_assoc] at k2
  exact (Units.mul_right_inj _).1 k2

end Pull

section Side

variable {S₀ S₁ : Scheme.{0}} {G : Over S₀} [GrpObj G] {A : Over S₁} [GrpObj A]
  {f : S₁ ⟶ S₀} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ) {S F : Type} [CommRing S] [CommRing F]
  {t : Spec (CommRingCat.of F) ⟶ S₁} {t₀ : Spec (CommRingCat.of S) ⟶ S₀} (g : S →+* F)
  (hτ : Spec.map (CommRingCat.ofHom g) ≫ t₀ = t ≫ f) {L₀ : LB G.left} {L₁ : LB A.left}

include hp hτ in

theorem exists_side_map (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen) (k : ℤ)
    (x : Over.mk t ⟶ A) (θ₀ : ThetaGrp G L₀ k (Over.mk t₀))
    (hx : Spec.map (CommRingCat.ofHom g) ≫ θ₀.pt.left = x.left ≫ φ)
    (π₀ : (Over.mk t₀ ⊗ G).left ⟶ Spec (CommRingCat.of S)) (hπ₀ : π₀ = (fst (Over.mk t₀) G).left)
    (π : (Over.mk t ⊗ A).left ⟶ Spec (CommRingCat.of F)) (hπ : π = (fst (Over.mk t) A).left) :
    ∃ (θ : ThetaGrp A L₁ k (Over.mk t))
      (mv : SecOver π₀ (LPow G L₀ k (Over.mk t₀)) →ₛₗ[g] SecOver π (LPow A L₁ k (Over.mk t))), θ.pt = x ∧
      (∀ s s', IsActOf G L₀ k θ₀ s s' → IsActOf A L₁ k θ (mv s) (mv s')) ∧
      (∀ (s : LB.Sec (LPow G L₀ k (Over.mk t₀)))
        (σ : LB.Sec (LB.LinComb L₀ (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => k))),
        IsPull (φ₁ := fun _ : Fin 1 => (snd (Over.mk t₀) G).left) (snd (Over.mk t₀) G).left s σ →
        PSec w (fun _ : Fin 1 => (snd (Over.mk t) A).left) (fun _ => 𝟙 G.left) (fun _ => k)
          ((snd (Over.mk t) A).left ≫ φ) (mv s) σ) ∧
      (Flat G.hom → ∀ (n : ℕ) (c : Fin n → F), (∀ a : Fin n → S, ∑ i, g (a i) * c i = 0 → ∀ i, a i = 0) →
        ∀ a : Fin n → SecOver π₀ (LPow G L₀ k (Over.mk t₀)), ∑ i, c i • mv (a i) = 0 → ∀ i, a i = 0) := by
  subst hπ₀ hπ
  obtain ⟨ψ, hψpb, hψsnd, hψeq⟩ := exists_psi hp (T := Over.mk t) (T₀ := Over.mk t₀)
    (Spec.map (CommRingCat.ofHom g)) hτ
  obtain ⟨θ, hθpt, hact⟩ := exists_theta_side hp (T := Over.mk t) (T₀ := Over.mk t₀)
    (Spec.map (CommRingCat.ofHom g)) hτ hL₀ hL₁ w hw k x θ₀ hx hψeq
  obtain ⟨mv, hmv⟩ := exists_moveMap (w := w) (φ' := fun _ : Fin 1 => (snd (Over.mk t) A).left)
    (φ := fun _ : Fin 1 => (snd (Over.mk t₀) G).left) (ε := fun _ => k)
    (π := (fst (Over.mk t₀) G).left) (π' := (fst (Over.mk t) A).left) (fS := g)
    hL₀ hL₁ hw (fun _ => hψsnd.symm) hψpb.w
  refine ⟨θ, mv, hθpt, fun s s' hs => ?_, fun s σ hs => ?_, fun hflat n c hc a e i => ?_⟩
  · exact hact s s' (mv s) (mv s') ((hmv s (mv s)).2 rfl) ((hmv s' (mv s')).2 rfl) hs
  · exact (psec_iff_of_isPull (fun _ => hψsnd.symm) hs hψsnd).1 ((hmv s (mv s)).2 rfl)
  · have := hflat
    have hfl : Flat (fst (Over.mk t₀) G).left := by
      rw [Over.fst_left]
      infer_instance
    exact move_indep hL₀ hL₁ (fun _ => hψsnd.symm) hψpb mv (fun s => (hmv s (mv s)).2 rfl) n c hc a e i

end Side

section Fam

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem isPull_famPull (hG : GlobalFnsSt) {k : ℕ} (F₀ : Fam D (FractionRing R) k) (α : D.X) (f : D.SecB k α)
    (h : GeneratorPullback.SecScal D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (F₀.s α) (D.famφB α) (DegPre.famε k) f
      (DegPre.prB D (FractionRing R)).left 1) :
    IsPull (DegPre.prB D F).left ((famPull D (FractionRing R) F hG k F₀).s α) f := by
  have hL : D.P.L.IsLB := D.P.isLB
  have hpZ : (DegPre.prB D (FractionRing R)).left ≫ specZIsTerminal.from _ =
      specZIsTerminal.from _ ≫ Spec.map (CommRingCat.ofHom (RingHom.id ℤ)) :=
    specZIsTerminal.hom_ext _ _
  have hφE : ∀ i, DegPre.famφ D (FractionRing R) α i = (DegPre.prB D (FractionRing R)).left ≫ D.famφB α i :=
    famφ_prB D (FractionRing R) α
  have h₁ : IsPull (DegPre.prB D (FractionRing R)).left (F₀.s α) f := by
    have key := isPull_pullOver (L := D.P.L) (ε := DegPre.famε k) hpZ hφE f
    rwa [eq_pullOver_of_secScal hL hpZ hφE h] at key
  have h₂ := isPull_pullOver (L := D.P.L) (ε := DegPre.famε k) (isPullback_famMap D (FractionRing R) F).w
    (famφ_famMap D (FractionRing R) F α) (F₀.s α)
  have hc : (famMap D (FractionRing R) F).left ≫ (DegPre.prB D (FractionRing R)).left = (DegPre.prB D F).left := by
    rw [← Over.comp_left, famMap_snd]
  exact IsPull.comp h₂ h₁ hc

end Fam

section Points

theorem pow_eq_one_of_injective {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G] [IsSeparated G.hom] {S F : Type}
    [CommRing S] [IsDomain S] [CommRing F] {g : S →+* F} (hg : Function.Injective g)
    {t₀ : Spec (CommRingCat.of S) ⟶ S₀} {t : Spec (CommRingCat.of F) ⟶ S₀} (ρ : Over.mk t ⟶ Over.mk t₀)
    (hρ : ρ.left = Spec.map (CommRingCat.ofHom g)) (x : Over.mk t₀ ⟶ G) {k : ℕ} (h : (ρ ≫ x) ^ k = 1) :
    x ^ k = 1 := by
  have hdom : IsDominant (Spec.map (CommRingCat.ofHom g)) := by
    rw [isDominant_iff]
    have hd : DenseRange (PrimeSpectrum.comap g) := by
      rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
      intro a ha
      rw [RingHom.mem_ker] at ha
      have ha0 : a = 0 := hg (by rw [ha, map_zero])
      rw [ha0]
      exact zero_mem _
    exact hd
  have e : ρ ≫ x ^ k = ρ ≫ 1 := by rw [MonObj.comp_pow, h, MonObj.comp_one]
  have : IsReduced (Over.mk t₀).left := show IsReduced (Spec (CommRingCat.of S)) from inferInstance
  apply Over.OverMorphism.ext
  have e' := congrArg (fun m => m.left) e
  simp only [Over.comp_left, hρ] at e'
  exact ext_of_isDominant_of_isSeparated G.hom (by simp only [Over.w]) (Spec.map (CommRingCat.ofHom g)) e'

end Points

end GlobalTheory.ThetaSpecialise
