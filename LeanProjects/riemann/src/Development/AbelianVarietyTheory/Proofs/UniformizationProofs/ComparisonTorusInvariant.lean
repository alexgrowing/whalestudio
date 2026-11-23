import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsAddEquivOfSplitTorusIso
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PulledComparisonEven
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TripleProductPointCompProjection
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TorusInvariance

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Units

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {H : Over S}

def pullTop {Z Y : Over S} (r : Z ⟶ Y) : Γ(Y.left, ⊤)ˣ →* Γ(Z.left, ⊤)ˣ :=
  Units.map r.left.appTop.hom.toMonoidHom

theorem pullTop_val {Z Y : Over S} (r : Z ⟶ Y) (a : Γ(Y.left, ⊤)ˣ) :
    (pullTop r a).val = r.left.appTop.hom a.val := rfl

theorem pullTop_comp {Z Y Y' : Over S} (r : Z ⟶ Y) (s : Y ⟶ Y') (a : Γ(Y'.left, ⊤)ˣ) :
    pullTop r (pullTop s a) = pullTop (r ≫ s) a :=
  Units.ext (SplitTorusHom.appTop_comp r s _).symm

theorem gm_pullTop {Z Y : Over S} (r : Z ⟶ Y) (a : Γ(Y.left, ⊤)ˣ) (z : Z.left) :
    gm (𝟙 Z.left) z ⊤ (pullTop r a) = gm r.left z ⊤ a := by
  apply Units.ext
  rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial]
  rfl

theorem exists_char [ConnectedSpace H.left] (ρ : Γ((splitTorus S X ⊗ H).left, ⊤)ˣ)
    (h : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ H),
      pullTop (lift (t * t') y) ρ = pullTop (lift t y) ρ * pullTop (lift t' y) ρ) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ H),
      pullTop (lift t y) ρ = pullTop t (charUnit S X χ) := by
  obtain ⟨χ, hχ, -⟩ := existsUnique_character_of_mul S X H ρ
    (fun Z t t' y => congrArg Units.val (h Z t t' y))
  refine ⟨χ, fun Z t y => ?_⟩
  have e : ρ = pullTop (fst (splitTorus S X) H) (charUnit S X χ) := Units.ext hχ
  rw [e, pullTop_comp, lift_fst]

theorem pullTop_eq_one [ConnectedSpace S] [ConnectedSpace H.left] [Module.Free ℤ X] [GrpObj H]
    (i : splitTorus S X ⟶ H) (ρ : Γ((splitTorus S X ⊗ H).left, ⊤)ˣ)
    (h₁ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X), pullTop (lift (t * t') 1) ρ =
      pullTop (lift t (t' ≫ i)) ρ * pullTop (lift t' 1) ρ)
    (h₂ : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ H),
      pullTop (lift (t * t') y) ρ * pullTop (lift t 1) ρ * pullTop (lift t' 1) ρ =
        pullTop (lift t y) ρ * pullTop (lift t' y) ρ * pullTop (lift (t * t') 1) ρ)
    (h₃ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X), pullTop (lift t⁻¹ 1) ρ = pullTop (lift t 1) ρ)
    (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ H) : pullTop (lift t y) ρ = 1 := by
  have hb : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ H),
      pullTop (lift t y) (ρ * (pullTop (lift (fst (splitTorus S X) H) (1 : _ ⟶ H)) ρ)⁻¹) =
        pullTop (lift t y) ρ * (pullTop (lift t 1) ρ)⁻¹ := fun Z t y => by
    rw [map_mul, map_inv, pullTop_comp, comp_lift, lift_fst, MonObj.comp_one]
  obtain ⟨χ, hχ⟩ := exists_char (ρ * (pullTop (lift (fst (splitTorus S X) H) (1 : _ ⟶ H)) ρ)⁻¹)
    (fun Z t t' y => by
      rw [hb, hb, hb]
      have := congrArg Additive.ofMul (h₂ Z t t' y)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at this ⊢
      linear_combination (norm := abel) this)
  have ind : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ H),
      pullTop (lift t y) ρ = pullTop (lift t 1) ρ := fun Z t y => by
    have := (hχ Z t y).trans (hχ Z t 1).symm
    rw [hb, hb] at this
    exact mul_right_cancel this
  have mul : ∀ (Z : Over S) (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ H),
      pullTop (lift (t * t') y) ρ = pullTop (lift t y) ρ * pullTop (lift t' y) ρ := fun Z t t' y => by
    rw [ind Z _ y, ind Z t y, ind Z t' y, h₁, ind Z t (t' ≫ i)]
  obtain ⟨ψ, hψ⟩ := exists_char ρ mul
  have zero : charUnit S X 0 = 1 := by
    have : charUnit S X (0 + 0) = charUnit S X 0 * charUnit S X 0 :=
      Units.ext (SplitTorusHom.charUnit_add 0 0)
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have one : pullTop (lift (1 : splitTorus S X ⟶ splitTorus S X) 1) ρ = 1 := by
    have := mul _ (1 : splitTorus S X ⟶ splitTorus S X) 1 1
    rw [_root_.mul_one] at this
    exact left_eq_mul.1 this
  have sq := mul _ (𝟙 (splitTorus S X)) (𝟙 (splitTorus S X))⁻¹ 1
  rw [mul_inv_cancel, one, h₃, hψ] at sq
  have e : pullTop (𝟙 (splitTorus S X)) (charUnit S X ψ) = charUnit S X ψ :=
    Units.ext (SplitTorusHom.appTop_id _)
  rw [e] at sq
  have two : ψ + ψ = 0 := SplitTorusHom.charUnit_injective (S := S) (by
    rw [SplitTorusHom.charUnit_add, zero]
    exact (congrArg Units.val sq).symm)
  have hψ0 : ψ = 0 := by
    rw [← two_smul ℤ] at two
    exact (smul_eq_zero.1 two).resolve_left two_ne_zero
  rw [hψ, hψ0, zero, map_one]

end Units

theorem exists_ratio {E B B' P : Scheme.{0}} {M : LB B} {M' : LB B'} (hM : M.IsLB) (hM' : M'.IsLB)
    {F : E ⟶ B} {F' : E ⟶ B'} (u : LB.Iso (M'.pull F') (M.pull F)) (hu : u.IsGen) (m s : P ⟶ E)
    (h : m ≫ F = s ≫ F) (h' : m ≫ F' = s ≫ F') :
    ∃ ρ : Γ(P, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) (j : M.ι) (j' : M'.ι),
      F (s (r z)) ∈ M.U j → F' (s (r z)) ∈ M'.U j' →
      gw u (r ≫ m) z j (fun _ => j') = gm r z ⊤ ρ * gw u (r ≫ s) z j (fun _ => j') := by
  have pg := (isGen_iff u).1 hu
  have pt : ∀ x : P, F (m x) = F (s x) := fun x => congrArg (fun g => g x) h
  have pt' : ∀ x : P, F' (m x) = F' (s x) := fun x => congrArg (fun g => g x) h'
  have gp : ∀ {Z : Scheme.{0}} (f : Z ⟶ E) (z : Z) (k k' : M'.ι), F' (f z) ∈ M'.U k → F' (f z) ∈ M'.U k' →
      gm f z ((M'.pull F').U (fun _ => k) ⊓ (M'.pull F').U (fun _ => k'))
        ((M'.pull F').g (fun _ => k) (fun _ => k')) = gm (f ≫ F') z _ (M'.g k k') := by
    intro Z f z k k' hk hk'
    have hp : f z ∈ (M'.pull F').U (fun _ => k) ⊓ (M'.pull F').U (fun _ => k') :=
      ⟨mem_pull.2 hk, mem_pull.2 hk'⟩
    show gm f z _ (∏ _k : PUnit, (res _ (pullU F' _ (M'.g k k'))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
    exact (gm_res f z _ hp _).trans (gm_pull f F' z (M'.U k ⊓ M'.U k') ⟨hk, hk'⟩ _)
  obtain ⟨W, hW⟩ : ∃ W : M.ι × M'.ι → P.Opens, ∀ p x, x ∈ W p ↔ F (s x) ∈ M.U p.1 ∧ F' (s x) ∈ M'.U p.2 :=
    ⟨fun p => s ⁻¹ᵁ (F ⁻¹ᵁ M.U p.1) ⊓ s ⁻¹ᵁ (F' ⁻¹ᵁ M'.U p.2), fun _ _ => Iff.rfl⟩
  have l₁ : ∀ p, W p ≤ m ⁻¹ᵁ ((M.pull F).U (fun _ => p.1) ⊓ (M'.pull F').U (fun _ => p.2)) := fun p x hx =>
    ⟨mem_pull.2 ((pt x).symm ▸ ((hW p x).1 hx).1), mem_pull.2 ((pt' x).symm ▸ ((hW p x).1 hx).2)⟩
  have l₂ : ∀ p, W p ≤ s ⁻¹ᵁ ((M.pull F).U (fun _ => p.1) ⊓ (M'.pull F').U (fun _ => p.2)) := fun p x hx =>
    ⟨mem_pull.2 ((hW p x).1 hx).1, mem_pull.2 ((hW p x).1 hx).2⟩
  obtain ⟨a, ha⟩ : ∃ a : ∀ p, Γ(P, W p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ P) (z : Z) p, r z ∈ W p →
      gm r z (W p) (a p) = gw u (r ≫ m) z p.1 (fun _ => p.2) * (gw u (r ≫ s) z p.1 (fun _ => p.2))⁻¹ :=
    ⟨fun p => res (l₁ p) (pullU m _ (u.s (fun _ => p.1, fun _ => p.2))) *
      (res (l₂ p) (pullU s _ (u.s (fun _ => p.1, fun _ => p.2))))⁻¹, fun Z r z p hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((gm_res r z (l₁ p) hz _).trans (gm_pull r m z _ (l₁ p hz) _)) ((map_inv _ _).trans (congrArg (·⁻¹)
          ((gm_res r z (l₂ p) hz _).trans (gm_pull r s z _ (l₂ p hz) _)))))⟩
  obtain ⟨ρ, hρ⟩ := glue_unit ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨j, hj⟩ := exists_chart hM (F (s x))
      obtain ⟨j', hj'⟩ := exists_chart hM' (F' (s x))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, j'), (hW _ x).2 ⟨hj, hj'⟩⟩) a (fun p q x hx => by
      have k₁ := (hW p x).1 hx.1
      have k₂ := (hW q x).1 hx.2
      rw [ha _ _ x p hx.1, ha _ _ x q hx.2, Category.id_comp, Category.id_comp,
        pg _ m x p.1 q.1 (fun _ => p.2) (fun _ => q.2) ((pt x).symm ▸ k₁.1) ((pt x).symm ▸ k₂.1)
          (mem_pull.2 ((pt' x).symm ▸ k₁.2)) (mem_pull.2 ((pt' x).symm ▸ k₂.2)),
        pg _ s x p.1 q.1 (fun _ => p.2) (fun _ => q.2) k₁.1 k₂.1 (mem_pull.2 k₁.2) (mem_pull.2 k₂.2),
        gp m x _ _ ((pt' x).symm ▸ k₁.2) ((pt' x).symm ▸ k₂.2), gp s x _ _ k₁.2 k₂.2, h, h', mul_inv,
        _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨ρ, fun Z r z j j' hj hj' => ?_⟩
  have hz : r z ∈ W (j, j') := (hW _ _).2 ⟨hj, hj'⟩
  have := (gm_res r z le_top hz ρ).symm.trans ((congrArg (gm r z (W (j, j'))) (hρ (j, j'))).trans (ha Z r z _ hz))
  rw [this, inv_mul_cancel_right]

section Level

open WCub EvenPull

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] {e : ℕ}

section One

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : UnifPre I D A G)

def wVal (e : ℕ) {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (N : (Z ⟶ G.left) → U.LG.L.ι) (r : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  gw (U.w e) r z (J (r ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ (fstG I e G).left))

theorem cube_val {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : Fin 3 → (T ⟶ thickObj R I e G))
    {z : T.left} {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {N : (T.left ⟶ G.left) → U.LG.L.ι}
    (hJ : Good D.toPre.P.L z J) (hN : Good U.LG.L z N) :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG x) z J =
      (∏ k : thK.{0}, wVal U e z J N (psum (thickObj R I e G) x k.down).left ^ thε k) *
        val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (tri (thick R I e) (fstG I e G) x) z N := by
  have := (U.gt e).q_hom
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x (U.gt e).q rfl
  let jM : thK → D.toPre.P.L.ι := fun k =>
    J (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)
  let jL : thK → U.LG.L.ι := fun k => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k)
  have mM : ∀ k, (tri (thick R I e) (U.gt e).pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k) z ∈
      D.toPre.P.L.U (jM k) := fun k => hJ _
  have mL : ∀ k, (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k) z ∈ U.LG.L.U (jL k) := fun k => hN _
  have e₂ := (clause_iff (tri (thick R I e) (U.gt e).pG x) (tri (thick R I e) (fstG I e G) x)
    (fun k : thK => (psum (thickObj R I e G) x k.down).left) _ _ _ (D.toPre.cub.t.s jM) (U.cubG.t.s jL)
    (fun k => (U.w e).s (fun _ => jM k, fun _ => jL k)) thε).1
    (U.w_cub e T x jL jM (fun a b e => congrArg N e) (fun a b e => congrArg J e)) z
    (Set.mem_iInter.2 mM) (Set.mem_iInter.2 mL) (fun k => ⟨mem_pull.2 (by
      have := mM k; rw [f₄ k] at this; exact this), mem_pull.2 (by
      have := mL k; rw [f₃ k] at this; exact this)⟩)
  refine e₂.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) rfl)
  unfold wVal
  rw [← f₃ k, ← f₄ k]
  rfl

theorem inv_pG : (ι[thickObj R I e G]).left ≫ (U.gt e).pG.left = (U.gt e).pG.left ≫ (ι[D.toPre.P.A]).left := by
  have := (U.gt e).q_hom
  exact inv_hom_fst _ _ (U.gt e).q

theorem even_val {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left)
    {z : Z} {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {N : (Z ⟶ G.left) → U.LG.L.ι}
    (hJ : Good D.toPre.P.L z J) (hN : Good U.LG.L z N) :
    val D.toPre.sym (r ≫ (U.gt e).pG.left) z J * wVal U e z J N r =
      wVal U e z J N (r ≫ (ι[thickObj R I e G]).left) * val U.symG (r ≫ (fstG I e G).left) z N := by
  have iF : (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left := inv_fst _ G
  have iP := inv_pG (e := e) U
  obtain ⟨jS, hS⟩ : ∃ jS : Fin 2 → U.LG.L.ι, ∀ k,
      N ((r ≫ (fstG I e G).left) ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) = jS k := ⟨_, fun _ => rfl⟩
  obtain ⟨jT, hT⟩ : ∃ jT : Fin 2 → D.toPre.P.L.ι, ∀ k, J ((r ≫ (U.gt e).pG.left) ≫
      (![(ι[D.toPre.P.A]).left, 𝟙 D.toPre.P.A.left] : Fin 2 → _) k) = jT k := ⟨_, fun _ => rfl⟩
  have S0 : N ((r ≫ (ι[thickObj R I e G]).left) ≫ (fstG I e G).left) = jS 0 := by
    rw [← hS, Category.assoc, iF, Category.assoc]; rfl
  have S1 : N (r ≫ (fstG I e G).left) = jS 1 := (congrArg N (Category.comp_id _)).symm.trans (hS 1)
  have T0 : J ((r ≫ (ι[thickObj R I e G]).left) ≫ (U.gt e).pG.left) = jT 0 := by
    rw [← hT, Category.assoc, iP, Category.assoc]; rfl
  have T1 : J (r ≫ (U.gt e).pG.left) = jT 1 := (congrArg J (Category.comp_id _)).symm.trans (hT 1)
  let W : (thickObj R I e G).left.Opens := (U.gt e).pG.left ⁻¹ᵁ (LB.LinComb D.toPre.P.L (K := Fin 2)
      ![(ι[D.toPre.P.A]).left, 𝟙 D.toPre.P.A.left] ![1, -1]).U jT ⊓
    ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jT 1) ⊓ (U.LG.L.pull (fstG I e G).left).U (fun _ => jS 1)) ⊓
    (ι[thickObj R I e G]).left ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jT 0) ⊓
      (U.LG.L.pull (fstG I e G).left).U (fun _ => jS 0)) ⊓
    (fstG I e G).left ⁻¹ᵁ (LB.LinComb U.LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]).U jS
  have hW : r z ∈ W := ⟨⟨⟨Set.mem_iInter.2 fun k => hT k ▸ hJ _, mem_pull.2 (T1 ▸ hJ _), mem_pull.2 (S1 ▸ hN _)⟩,
    mem_pull.2 (T0 ▸ hJ _), mem_pull.2 (S0 ▸ hN _)⟩, Set.mem_iInter.2 fun k => hS k ▸ hN _⟩
  have l₁ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_left)
  have l₂ : W ≤ _ := inf_le_left.trans (inf_le_left.trans inf_le_right)
  have l₃ : W ≤ _ := inf_le_left.trans inf_le_right
  have l₄ : W ≤ _ := inf_le_right
  obtain ⟨n₁, n₂⟩ := even_stalk (U.w e) U.symG D.toPre.sym jS jT W l₁ l₂ l₃ l₄ r z hW
  have E := n₁.symm.trans ((congrArg (gm r z W) (U.w_even e jS jT
    (fun a b h => by rw [← hS, ← hS, Category.assoc, Category.assoc]; exact congrArg (fun q => N (r ≫ q)) h)
    (fun a b h => by rw [← hT, ← hT, Category.assoc, Category.assoc]; exact congrArg (fun q => J (r ≫ q)) h)
    W l₁ l₂ l₃ l₄)).trans n₂)
  rw [val_of _ _ z J jT hT, val_of _ _ z N jS hS, wVal, wVal, S0, S1, T0, T1]
  exact E

end One

section Two

variable {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {U : UnifPre I D A G}
  {U' : UnifPre I D' A' G}
  (u : LB.Iso (D'.toPre.P.L.pull (U'.gt e).pG.left) (D.toPre.P.L.pull (U.gt e).pG.left))

def uVal {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
    (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι) (r : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  gw u r z (J (r ≫ (U.gt e).pG.left)) (fun _ => J' (r ≫ (U'.gt e).pG.left))

variable {wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))}
  (sq : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
    (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM →
    (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL →
    (fstG I e G).left (r z) ∈ U'.LG.L.U jL' →
    gw u r z jM (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') =
      gw (U.w e) r z jM (fun _ => jL) * gw wL (r ≫ (fstG I e G).left) z jL jL')
include sq

theorem cube_uVal (hc : PMaps wL (thφ G (x3 G)) (thφ G (x3 G)) thε U'.cubG.t U.cubG.t (𝟙 _))
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (x : Fin 3 → (T ⟶ thickObj R I e G))
    {z : T.left} {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) (hJ' : Good D'.toPre.P.L z J') :
    val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
        (tri (thick R I e) (U.gt e).pG x) z J =
      (∏ k : thK.{0}, uVal u z J J' (psum (thickObj R I e G) x k.down).left ^ thε k) *
        val (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
          (tri (thick R I e) (U'.gt e).pG x) z J' := by
  choose N hN using fun χ : T.left ⟶ G.left => exists_chart U.LG.isLB (χ z)
  choose N' hN' using fun χ : T.left ⟶ G.left => exists_chart U'.LG.isLB (χ z)
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x (𝟙 _) (Category.id_comp _).symm
  have e₁ := cube_val U x hJ hN
  have e₂ := cube_val U' x hJ' hN'
  have e₃ := hc _ (tri (thick R I e) (fstG I e G) x) z
    (fun k => N (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k))
    (fun k => N' (tri (thick R I e) (fstG I e G) x ≫ thφ G (x3 G) k)) (fun k => hN _) (fun k => hN' _)
  rw [Category.comp_id] at e₃
  have e₄ : val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε) U.cubG.t (tri (thick R I e) (fstG I e G) x) z N =
      (∏ k : thK.{0}, gw wL ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left) z
        (N ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left))
        (N' ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left)) ^ thε k) *
      val (L := U'.LG.L) (φ := thφ G (x3 G)) (ε := thε) U'.cubG.t (tri (thick R I e) (fstG I e G) x) z N' :=
    e₃.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => by rw [f₃ k]) rfl)
  rw [e₁, e₂, e₄, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [← mul_zpow, ← mul_zpow]
  exact congrArg (· ^ thε k) (sq _ _ z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)).symm

theorem even_uVal (hs : PMaps wL (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1]
      U'.symG U.symG (𝟙 G.left))
    {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) {z : Z}
    {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι} {J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) (hJ' : Good D'.toPre.P.L z J') :
    val D.toPre.sym (r ≫ (U.gt e).pG.left) z J * uVal u z J J' r =
      uVal u z J J' (r ≫ (ι[thickObj R I e G]).left) * val D'.toPre.sym (r ≫ (U'.gt e).pG.left) z J' := by
  choose N hN using fun χ : Z ⟶ G.left => exists_chart U.LG.isLB (χ z)
  choose N' hN' using fun χ : Z ⟶ G.left => exists_chart U'.LG.isLB (χ z)
  have iF : (ι[thickObj R I e G]).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left := inv_fst _ G
  have e₁ := even_val U r hJ hN
  have e₂ := even_val U' r hJ' hN'
  have e₃ := hs _ (r ≫ (fstG I e G).left) z
    (fun k => N ((r ≫ (fstG I e G).left) ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k))
    (fun k => N' ((r ≫ (fstG I e G).left) ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k)) (fun k => hN _) (fun k => hN' _)
  rw [Category.comp_id, Fin.prod_univ_two] at e₃
  let d := fun s : Z ⟶ G.left => gw wL s z (N s) (N' s)
  have e₄ : val U.symG (r ≫ (fstG I e G).left) z N =
      d ((r ≫ (ι[thickObj R I e G]).left) ≫ (fstG I e G).left) * (d (r ≫ (fstG I e G).left))⁻¹ *
        val U'.symG (r ≫ (fstG I e G).left) z N' := by
    refine e₃.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) ((zpow_one _).trans (congrArg d ?_))
      ((zpow_neg_one _).trans (congrArg (fun s => (d s)⁻¹) (Category.comp_id _)))) rfl)
    rw [Category.assoc r (ι[thickObj R I e G]).left, iF, Category.assoc]; rfl
  have e₅ : ∀ s : Z ⟶ (thickObj R I e G).left, uVal u z J J' s * wVal U' e z J' N' s =
      wVal U e z J N s * d (s ≫ (fstG I e G).left) := fun s => sq _ s z _ _ _ _ (hJ _) (hJ' _) (hN _) (hN' _)
  have a₁ := congrArg Additive.ofMul e₁
  have a₂ := congrArg Additive.ofMul e₂
  have a₄ := congrArg Additive.ofMul e₄
  have a₅ := congrArg Additive.ofMul (e₅ r)
  have a₆ := congrArg Additive.ofMul (e₅ (r ≫ (ι[thickObj R I e G]).left))
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv] at a₁ a₂ a₄ a₅ a₆ ⊢
  linear_combination (norm := abel) a₁ - a₂ + a₄ + a₅ - a₆

end Two

end Level

theorem prod_psum {S : Scheme.{0}} {H T : Over S} [GrpObj H] [IsCommMonObj H] (x x' y : T ⟶ H) {V : Type}
    [CommGroup V] (h : (T.left ⟶ H.left) → V) :
    ∏ k : thK.{0}, h (psum H ![x, x', y] k.down).left ^ thε k =
      h (x * x' * y).left * (h (x * x').left)⁻¹ * (h (x * y).left)⁻¹ * (h (x' * y).left)⁻¹ * h x.left * h x'.left *
        h y.left * (h (1 : T ⟶ H).left)⁻¹ := by
  have e : ∀ k : thK, (lift x (lift x' y)).left ≫ thφ H (x3 H) k = (psum H ![x, x', y] k.down).left := fun k =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x (lift x' y))) (x3 H) k.down).trans
      (congrArg (fun q => psum H q k.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])))
  rw [← prod_cub x x' y h]
  exact Finset.prod_congr rfl fun k _ => by rw [e k]

theorem tri_congr {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {a b a' b' : T ⟶ thickObj R I e G}
    (c : T ⟶ thickObj R I e G) (ha : a ≫ g.q = a' ≫ g.q) (hb : b ≫ g.q = b' ≫ g.q) :
    WCub.tri (thick R I e) g.pG ![a, b, c] = WCub.tri (thick R I e) g.pG ![a', b', c] := by
  show (lift (TorusCoord.im g a) (lift (TorusCoord.im g b) (TorusCoord.im g c))).left =
    (lift (TorusCoord.im g a') (lift (TorusCoord.im g b') (TorusCoord.im g c))).left
  rw [TorusCoord.im_congr g ha, TorusCoord.im_congr g hb]

theorem pG_congr {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} {a a' : T ⟶ thickObj R I e G}
    (ha : a ≫ g.q = a' ≫ g.q) : a.left ≫ g.pG.left = a'.left ≫ g.pG.left :=
  congrArg (fun q => q.left) (TorusCoord.im_congr g ha)

theorem connectedSpace_spec_quotient {R : Type} [CommRing R] [IsLocalRing R] (J : Ideal R)
    (p : Spec (CommRingCat.of (R ⧸ J))) : ConnectedSpace (Spec (CommRingCat.of (R ⧸ J))) := by
  have : Nontrivial (R ⧸ J) := PrimeSpectrum.nontrivial p
  have : IsLocalRing (R ⧸ J) := IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  have : PreconnectedSpace (PrimeSpectrum (R ⧸ J)) :=
    ⟨isPreconnected_of_forall (IsLocalRing.closedPoint (R ⧸ J)) fun y _ =>
      ⟨closure {y}, Set.subset_univ _, (IsLocalRing.specializes_closedPoint y).mem_closure, subset_closure rfl,
        isPreconnected_singleton.closure⟩⟩
  exact (⟨⟨p⟩⟩ : ConnectedSpace (PrimeSpectrum (R ⧸ J)))

theorem ratio_eq_one {S : Scheme.{0}} {X : Type} [AddCommGroup X] {H : Over S} [ConnectedSpace S]
    [ConnectedSpace H.left] [Module.Free ℤ X] [GrpObj H] [IsCommMonObj H]
    (i : splitTorus S X ⟶ H) [IsMonHom i] (ρ : Γ((splitTorus S X ⊗ H).left, ⊤)ˣ)
    (h : ∀ (Z : Over S) (z : Z.left), ∃ a : (Z.left ⟶ H.left) → (Z.left.presheaf.stalk z)ˣ,
      (∀ (t : Z ⟶ splitTorus S X) (y : Z ⟶ H),
        a ((t ≫ i) * y).left = gm (𝟙 Z.left) z ⊤ (pullTop (lift t y) ρ) * a y.left) ∧
      (∀ (t t' : Z ⟶ splitTorus S X) (y : Z ⟶ H),
        ∏ k : thK.{0}, a (psum H ![t ≫ i, t' ≫ i, y] k.down).left ^ thε k =
          ∏ k : thK.{0}, a (psum H ![1, 1, y] k.down).left ^ thε k) ∧
      ∀ t : Z ⟶ splitTorus S X, a ((t ≫ i).left ≫ (ι[H]).left) * a (1 : Z ⟶ H).left =
        a (t ≫ i).left * a ((1 : Z ⟶ H).left ≫ (ι[H]).left))
    (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ H) : pullTop (lift t y) ρ = 1 := by
  choose a k c s using h
  have o : ∀ (Z : Over S) (z : Z.left) (t : Z ⟶ splitTorus S X), a Z z (t ≫ i).left =
      gm (𝟙 Z.left) z ⊤ (pullTop (lift t 1) ρ) * a Z z (1 : Z ⟶ H).left := fun Z z t => by
    have := k Z z t 1
    rwa [_root_.mul_one] at this
  refine pullTop_eq_one i ρ (fun Z t t' => unit_ext fun z _ => ?_) (fun Z t t' y => unit_ext fun z _ => ?_)
    (fun Z t => unit_ext fun z _ => ?_) Z t y
  · have e := o Z z (t * t')
    rw [MonObj.mul_comp, k, o, ← _root_.mul_assoc] at e
    rw [map_mul]
    exact (mul_right_cancel e).symm
  · have e := c Z z t t' y
    rw [prod_psum, prod_psum, ← MonObj.mul_comp t t', _root_.one_mul, _root_.one_mul, k, k, k, o, o, o] at e
    have d := congrArg Additive.ofMul e
    apply Additive.ofMul.injective
    simp only [map_mul, ofMul_mul, ofMul_inv] at d ⊢
    linear_combination (norm := abel) d
  · have e := s Z z t
    have i₁ : (t ≫ i) ≫ ι[H] = t⁻¹ ≫ i := by rw [GrpObj.inv_comp, Hom.inv_def]
    have i₂ : (1 : Z ⟶ H) ≫ ι[H] = 1 := by rw [← Hom.inv_def, inv_one]
    rw [← Over.comp_left, ← Over.comp_left, i₁, i₂, o, o] at e
    exact mul_right_cancel (mul_right_cancel e)

theorem cancel_even {V : Type} [CommGroup V] {s s' a b c d : V} (h : s * a = b * s') (h' : s * c = d * s') :
    b * c = a * d := by
  have e := congrArg Additive.ofMul h
  have e' := congrArg Additive.ofMul h'
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at e e' ⊢
  linear_combination (norm := abel) e' - e

theorem exists_ratio_translate {S B B' : Scheme.{0}} {T H : Over S} [GrpObj H] (i : T ⟶ H) {M : LB B} {M' : LB B'}
    (hM : M.IsLB) (hM' : M'.IsLB) {F : H.left ⟶ B} {F' : H.left ⟶ B'} (u : LB.Iso (M'.pull F') (M.pull F))
    (hu : u.IsGen) (h : ∀ (Z : Over S) (t : Z ⟶ T) (y : Z ⟶ H), ((t ≫ i) * y).left ≫ F = y.left ≫ F)
    (h' : ∀ (Z : Over S) (t : Z ⟶ T) (y : Z ⟶ H), ((t ≫ i) * y).left ≫ F' = y.left ≫ F') :
    ∃ ρ : Γ((T ⊗ H).left, ⊤)ˣ, ∀ (Z : Over S) (t : Z ⟶ T) (y : Z ⟶ H) (z : Z.left) (j : M.ι) (j' : M'.ι),
      F (y.left z) ∈ M.U j → F' (y.left z) ∈ M'.U j' →
      gw u ((t ≫ i) * y).left z j (fun _ => j') =
        gm (𝟙 Z.left) z ⊤ (pullTop (lift t y) ρ) * gw u y.left z j (fun _ => j') := by
  obtain ⟨ρ, hρ⟩ := exists_ratio hM hM' u hu ((fst T H ≫ i) * snd T H).left (snd T H).left (h _ _ _) (h' _ _ _)
  refine ⟨ρ, fun Z t y z j j' m m' => ?_⟩
  have a : (lift t y).left ≫ (snd T H).left = y.left := by rw [← Over.comp_left, lift_snd]
  have b : (snd T H).left ((lift t y).left z) = y.left z := congrArg (fun g => g z) a
  have := hρ _ (lift t y).left z j j' (b.symm ▸ m) (b.symm ▸ m')
  rwa [a, ← Over.comp_left, MonObj.comp_mul, lift_fst_assoc, lift_snd, ← gm_pullTop] at this

end TorusInvariance

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TorusInvariance in
set_option maxHeartbeats 400000 in

theorem comparison_torus_invariant : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → (Geo.Tor.PMaps wL (thφ G (x3 G)) (thφ G (x3 G)) thε U'.cubG.t U.cubG.t (𝟙 _) ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] U'.symG U.symG (𝟙 G.left)) → ∀ (e : ℕ) (β : thickObj R I e D'.toPre.P.A ≅ thickObj R I e D.toPre.P.A), IsMonHom β.hom → (U'.gt e).q ≫ β.hom = (U.gt e).q → ∀ u : LB.Iso (D'.toPre.P.L.pull (U'.gt e).pG.left) (D.toPre.P.L.pull (U.gt e).pG.left), u.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw u r z jM (fun _ => jM') * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL') → ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (τ : Z ⟶ splitTorus _ D.toPre.X) (y : Z ⟶ thickObj R I e G) (z : Z.left) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι), (U.gt e).pG.left (y.left z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (y.left z) ∈ D'.toPre.P.L.U jM' → Geo.Tor.gw u ((τ ≫ (U.gt e).i) * y).left z jM (fun _ => jM') = Geo.Tor.gw u y.left z jM (fun _ => jM') := by
  intro _ R _ _ _ I _ D D' A A' G _ _ hG U U' wL _ _ _ ⟨hc, hs⟩ e β _ hβ u hu sq Z₀ τ₀ y₀ z₀ jM jM' m m'
  have := (U.gt e).q_hom
  have := (U'.gt e).q_hom
  have := (U.gt e).i_hom
  have := hG.geomConnected
  have := connectedSpace_spec_quotient (I ^ (e + 1)) (Z₀.hom z₀)
  have : GeometricallyConnected (thickObj R I e G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
  have : ConnectedSpace (thickObj R I e G).left :=
    GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
  have hq : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X),
      (τ ≫ (U.gt e).i) ≫ (U.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U.gt e).q := fun τ => by
    rw [Category.assoc, (U.gt e).isKernel.w, MonObj.one_comp, ← Category.assoc, comp_toUnit, Hom.one_def]
  have hq' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X),
      (τ ≫ (U.gt e).i) ≫ (U'.gt e).q = (1 : Z ⟶ thickObj R I e G) ≫ (U'.gt e).q := fun τ => by
    rw [← cancel_mono β.hom, Category.assoc _ _ β.hom, Category.assoc _ _ β.hom, hβ]
    exact hq τ
  have hp : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U.gt e).pG.left = y.left ≫ (U.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq, ← MonObj.mul_comp, _root_.one_mul])
  have hp' : ∀ {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : Z ⟶ splitTorus _ D.toPre.X)
      (y : Z ⟶ thickObj R I e G), ((τ ≫ (U.gt e).i) * y).left ≫ (U'.gt e).pG.left = y.left ≫ (U'.gt e).pG.left :=
    fun τ y => pG_congr _ (by rw [MonObj.mul_comp, hq', ← MonObj.mul_comp, _root_.one_mul])
  obtain ⟨ρ, key⟩ := exists_ratio_translate (U.gt e).i D.toPre.P.isLB D'.toPre.P.isLB u hu
    (fun _ => hp) (fun _ => hp')
  have triv := ratio_eq_one (U.gt e).i ρ (fun Z z => by
    choose J hJ using fun χ : Z.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ z)
    choose J' hJ' using fun χ : Z.left ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (χ z)
    refine ⟨uVal u z J J', fun t y => ?_, fun t t' y => ?_, fun t => ?_⟩
    · rw [uVal, uVal, hp, hp']
      exact key Z t y z _ _ (hJ _) (hJ' _)
    · have a := cube_uVal u sq hc ![t ≫ (U.gt e).i, t' ≫ (U.gt e).i, y] hJ hJ'
      have b := cube_uVal u sq hc ![1, 1, y] hJ hJ'
      rw [tri_congr (U.gt e) y (hq t) (hq t'), tri_congr (U'.gt e) y (hq' t) (hq' t')] at a
      exact mul_right_cancel (a.symm.trans b)
    · have a := even_uVal u sq hs (t ≫ (U.gt e).i).left hJ hJ'
      have b := even_uVal u sq hs (1 : Z ⟶ thickObj R I e G).left hJ hJ'
      rw [pG_congr (U.gt e) (hq t), pG_congr (U'.gt e) (hq' t)] at a
      exact cancel_even a b)
  rw [key Z₀ τ₀ y₀ z₀ jM jM' m m', triv, map_one, _root_.one_mul]

end GlobalTheory
