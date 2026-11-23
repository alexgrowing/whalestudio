import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarriedOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecCarried
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOfTheoremOfCubeTenPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.CubeCarried

section
variable {X Y Y' Z : Scheme.{0}}

theorem gs_comp (g : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (h : f (g z) ∈ U) (a : Γ(X, U)) :
    gs (g ≫ f) z U a = (g.stalkMap z).hom (gs f (g z) U a) := by
  rw [← gs_pull g f z U h, gs_eq_map_gs g z (f ⁻¹ᵁ U) h, gs_eq (𝟙 Y) (g z) (f ⁻¹ᵁ U) h, gs_eq f (g z) U h]
  rfl

theorem gm_val_map (g : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : g z ∈ U) (a : Γ(Y, U)ˣ) :
    (gm g z U a).val = (g.stalkMap z).hom (gm (𝟙 Y) (g z) U a).val := by
  rw [gm_eq_map_gm g z U h]; rfl

variable {L : LB X} {Γ' : Type} {F : Γ' → (X ⟶ X)}

def CTriv (w : ∀ σ, LB.Iso L (L.pull (F σ))) (Y : Scheme.{0}) (Rel : Γ' → ∀ Z : Scheme.{0}, (Z ⟶ Y) → (Z ⟶ Y) → Prop)
    (S : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y ⟶ X) → U), ∏ k, h (φ k) ^ ε k = S U h) ∧
    ∀ σ (Z : Scheme.{0}) (r r' : Z ⟶ Y) (z : Z) J J', Rel σ Z r r' → Good L z J → Good L z J' →
      val t r' z J = S _ (fun ψ => gw (w σ) (r ≫ ψ) z (J (r' ≫ ψ)) (J' (r ≫ ψ))) * val t r z J'

variable {w : ∀ σ, LB.Iso L (L.pull (F σ))} {Rel : Γ' → ∀ Z : Scheme.{0}, (Z ⟶ Y) → (Z ⟶ Y) → Prop}

theorem CTriv.mul {S S' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv w Y Rel S) (h' : CTriv w Y Rel S') :
    CTriv w Y Rel (fun U _ g => S U g * S' U g) := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', e', c'⟩ := h'
  refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ g => (Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (e U g) (e' U g)), ?_⟩
  intro σ Z r r' z J J' hr hJ hJ'
  rw [val_mul hJ, val_mul hJ', c σ Z r r' z J J' hr hJ hJ', c' σ Z r r' z J J' hr hJ hJ', _root_.mul_mul_mul_comm]

theorem CTriv.inv {S : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv w Y Rel S) :
    CTriv w Y Rel (fun U _ g => (S U g)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ g => ?_, ?_⟩
  · simp only [zpow_neg, Finset.prod_inv_distrib, e U g]
  · intro σ Z r r' z J J' hr hJ hJ'
    rw [val_inv, val_inv, c σ Z r r' z J J' hr hJ hJ', mul_inv]

theorem CTriv.pull {S : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv w Y Rel S) (q : Y' ⟶ Y)
    {Rel' : Γ' → ∀ Z : Scheme.{0}, (Z ⟶ Y') → (Z ⟶ Y') → Prop}
    (hq : ∀ σ Z r r', Rel' σ Z r r' → Rel σ Z (r ≫ q) (r' ≫ q)) :
    CTriv w Y' Rel' (fun U _ g => S U (fun ψ => g (q ≫ ψ))) := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  refine ⟨K, inferInstance, _, _, LB.pullGen L φ ε t q, DVR.pullGen_isGen _ _ _ _ ht _,
    fun U _ g => e U (fun ψ => g (q ≫ ψ)), ?_⟩
  intro σ Z r r' z J J' hr hJ hJ'
  rw [val_pull hJ, val_pull hJ', c σ Z _ _ z J J' (hq _ _ _ _ hr) hJ hJ']
  simp only [Category.assoc]

theorem CTriv.congr {S S' : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv w Y Rel S)
    (hS : ∀ (U : Type) [CommGroup U] g, S U g = S' U g) : CTriv w Y Rel S' := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  exact ⟨K, inferInstance, φ, ε, t, ht, fun U _ g => (e U g).trans (hS U g),
    fun σ Z r r' z J J' hr hJ hJ' => (c σ Z r r' z J J' hr hJ hJ').trans (by rw [hS])⟩

theorem ctriv_of_pmaps {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (H : Γ' → (Y ⟶ Y)) (hc : ∀ σ k, φ k ≫ F σ = H σ ≫ φ k) (hp : ∀ σ, PMaps (w σ) φ φ ε t t (H σ)) :
    CTriv w Y (fun σ _ r r' => r' = r ≫ H σ) (fun _ _ h => ∏ k, h (φ k) ^ ε k) := by
  refine ⟨K, inferInstance, φ, ε, t, ht, fun _ _ _ => rfl, ?_⟩
  rintro σ Z r _ z J J' rfl hJ hJ'
  refine hp σ Z r z _ _ (fun k => ?_) (fun k => hJ' (r ≫ φ k))
  have := hJ ((r ≫ H σ) ≫ φ k)
  rw [← pt_eq (hc σ)]
  exact this

theorem ctriv_of_sec (θ : L.Sec) (hθ : ∀ σ, SecCarried L θ (F σ) (w σ)) (f : Y ⟶ X) (hf : ∀ y, f y ∈ secNz θ)
    (hR : ∀ σ Z r r', Rel σ Z r r' → r' ≫ f = (r ≫ f) ≫ F σ) : CTriv w Y Rel (fun _ _ g => g f) := by
  have hu : ∀ j, IsUnit ((SpecialFibreGenerator.secAlong θ f).f j) := fun j =>
    Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hf y)
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (SpecialFibreGenerator.mem_nonzeroLocus_secAlong θ f hi)
      exact (Y.mem_basicOpen _ y hy).1 (SpecialFibreGenerator.mem_basicOpen_of_chart _ hy hk)
  let t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ ↦ f) fun _ ↦ ((1 : ℕ) : ℤ)) := ⟨fun j => (hu j).unit⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, Good L z J →
      (val t r z J).val = gs (r ≫ f) z (L.U (J (r ≫ f))) (θ.f _) := by
    intro Z r z J hJ
    have hm := hJ.mem (fun _ : Fin 1 => f) r
    refine (gs_unit r z _ hm _).symm.trans ?_
    refine Eq.trans ?_ (gs_pull r f z _ (hJ (r ≫ f)) _)
    exact gs_res r z (LB.wchart_le L (fun _ : Fin 1 => f) (fun _ => J (r ≫ f)) 0) hm _
  refine ⟨Fin 1, inferInstance, _, _, t,
    fun i j => Units.ext ((SpecialFibreGenerator.secAlong θ f).compat i j), fun U _ g => by simp, ?_⟩
  intro σ Z r r' z J J' hr hJ hJ'
  apply Units.ext
  beta_reduce
  rw [Units.val_mul, v _ _ _ _ hJ, v _ _ _ _ hJ']
  have hj := hJ (r' ≫ f)
  have hk := hJ' (r ≫ f)
  generalize J (r' ≫ f) = j at hj ⊢
  generalize J' (r ≫ f) = k at hk ⊢
  rw [hR σ Z r r' hr] at hj ⊢
  generalize r ≫ f = g at hj hk ⊢
  have hj' : F σ (g z) ∈ L.U j := hj
  have e := hθ σ (g z) j k hk hj'
  rw [gs_comp g (F σ) z _ hj', gs_eq_map_gs g z _ hk, gs_eq _ _ _ hj', e, map_mul, gs_eq (𝟙 X) (g z) _ hk]
  exact congrArg₂ (· * ·) (gm_val_map g z ((L.pull (F σ)).U (fun _ => j) ⊓ L.U k)
    ⟨mem_pull.2 hj', hk⟩ _).symm rfl

theorem CTriv.exists_gen (hL : L.IsLB) {S : ∀ (U : Type) [CommGroup U], ((Y ⟶ X) → U) → U} (h : CTriv w Y Rel S)
    (f : Y ⟶ X) (hf : ∀ (U : Type) [CommGroup U] (g : (Y ⟶ X) → U), S U g = g f) :
    ∃ t : LB.Gen (L.pull f), t.IsGen ∧ ∀ σ (Z : Scheme.{0}) (r r' : Z ⟶ Y) (z : Z) (j k : L.ι), Rel σ Z r r' →
      f (r' z) ∈ L.U j → f (r z) ∈ L.U k →
      gm r' z ((L.pull f).U (fun _ => j)) (t.s (fun _ => j)) =
        gw (w σ) (r ≫ f) z j k * gm r z ((L.pull f).U (fun _ => k)) (t.s (fun _ => k)) := by
  obtain ⟨K, _, φ, ε, t, ht, e, c⟩ := h
  obtain ⟨t', ht', v⟩ := Geo.Tor.exists_gen hL (φ' := fun _ : PUnit => f) (ε' := fun _ => 1)
    (fun U _ g => by rw [e, hf]; simp) t ht
  refine ⟨t', ht', fun σ Z r r' z j k hr hj hk => ?_⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good L hL z (fun _ : PUnit => r' ≫ f) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hj)
  obtain ⟨J', hJ', eJ'⟩ := exists_good L hL z (fun _ : PUnit => r ≫ f) (fun _ => k) (fun _ _ _ => rfl) (fun _ => hk)
  have := c σ Z r r' z J J' hr hJ hJ'
  rw [← v _ _ _ _ hJ, ← v _ _ _ _ hJ', hf, val_of t' r' z J (fun _ => j) eJ, val_of t' r z J' (fun _ => k) eJ',
    eJ ⟨⟩, eJ' ⟨⟩] at this
  exact this

end

section Grp

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem psum_single {T : Over S} (x : Fin 3 → (T ⟶ G)) (i : Fin 3) : psum G x {i} = x i := by
  fin_cases i <;> exact _root_.mul_one _

theorem groupPullback_tripleProductMap_lift (m : CubeMap G G) {T T' : Over S} (h : T'.left ⟶ T.left) (x' y' z' : T' ⟶ G) (x y z : T ⟶ G)
    (hx : x'.left ≫ m.F = h ≫ x.left) (hy : y'.left ≫ m.F = h ≫ y.left) (hz : z'.left ≫ m.F = h ≫ z.left) :
    (lift x' (lift y' z')).left ≫ m.F3 = h ≫ (lift x (lift y z)).left := by
  have key : ∀ i, ((lift x' (lift y' z')).left ≫ m.F3) ≫ (x3 G i).left =
      (lift x' (lift y' z') ≫ x3 G i).left ≫ m.F := fun i => by
    have := m.psum_comm {i}
    rw [psum_single] at this
    rw [Category.assoc, ← this, Over.comp_left, Category.assoc]
  have key' : ∀ i, (h ≫ (lift x (lift y z)).left) ≫ (x3 G i).left = h ≫ (lift x (lift y z) ≫ x3 G i).left :=
    fun i => by rw [Category.assoc, Over.comp_left]
  have e : ∀ i, ((lift x' (lift y' z')).left ≫ m.F3) ≫ (x3 G i).left =
      (h ≫ (lift x (lift y z)).left) ≫ (x3 G i).left := fun i => by
    rw [key, key']
    fin_cases i
    · simpa [x3] using hx
    · simpa [x3] using hy
    · simpa [x3] using hz
  apply pullback.hom_ext
  · exact e 0
  · apply pullback.hom_ext
    · exact (Category.assoc _ _ _).trans ((e 1).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((e 2).trans (Category.assoc _ _ _).symm)

variable {L : RigLB G} {Γ' : Type} {s : Γ' → (S ⟶ S)} {F : Γ' → (G.left ⟶ G.left)}

theorem exists_gen_carried (cb : CubicalStr G L) (hF : ∀ σ, IsGrpPullback G G (s σ) (F σ))
    (w : ∀ σ, LB.Iso L.L (L.L.pull (F σ)))
    (hrig : ∀ σ, PMaps (w σ) (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (s σ))
    (hcub : ∀ σ, PMaps (w σ) (thφ G (x3 G)) (thφ G (x3 G)) thε cb.t cb.t (cubeMapOf (hF σ)).F3)
    (θ : L.L.Sec) (hθ : ∀ σ, SecCarried L.L θ (F σ) (w σ)) (T : Over S) (H : Γ' → (T.left ⟶ T.left))
    (hH : ∀ σ, H σ ≫ T.hom = T.hom ≫ s σ) (x a b c : T ⟶ G)
    (hx : ∀ σ, x.left ≫ F σ = H σ ≫ x.left) (ha : ∀ σ, a.left ≫ F σ = H σ ≫ a.left)
    (hb : ∀ σ, b.left ≫ F σ = H σ ≫ b.left) (hc : ∀ σ, c.left ≫ F σ = H σ ≫ c.left) (W : T.left.Opens)
    (hW : ∀ f ∈ cubeTen x a b c, W ≤ f.left ⁻¹ᵁ secNz θ) :
    ∃ t : LB.Gen (L.L.pull (W.ι ≫ x.left)), t.IsGen ∧
      ∀ σ (Z : Scheme.{0}) (r r' : Z ⟶ W) (z : Z) (j k : L.L.ι), r' ≫ W.ι = (r ≫ W.ι) ≫ H σ →
      (W.ι ≫ x.left) (r' z) ∈ L.L.U j → (W.ι ≫ x.left) (r z) ∈ L.L.U k →
      gm r' z ((L.L.pull (W.ι ≫ x.left)).U (fun _ => j)) (t.s (fun _ => j)) =
        gw (w σ) (r ≫ W.ι ≫ x.left) z j k * gm r z ((L.L.pull (W.ι ≫ x.left)).U (fun _ => k)) (t.s (fun _ => k)) := by
  let P : (T ⟶ G) → Prop := fun u => ∀ σ, u.left ≫ F σ = H σ ≫ u.left
  have mul : ∀ {u v}, P u → P v → P (u * v) := fun hu hv σ =>
    ((GlobalTheory.Mum.grpPullback_points_lift_mul_inv _ _ _ G G _ (hF σ) T T (H σ) (hH σ)).2 _ _ _ _ (hu σ) (hv σ)).1
  have inv : ∀ {u}, P u → P u⁻¹ := fun hu σ =>
    ((GlobalTheory.Mum.grpPullback_points_lift_mul_inv _ _ _ G G _ (hF σ) T T (H σ) (hH σ)).2 _ _ _ _ (hu σ) (hu σ)).2
  let Rel : Γ' → ∀ Z : Scheme.{0}, (Z ⟶ W) → (Z ⟶ W) → Prop := fun σ Z r r' => r' ≫ W.ι = (r ≫ W.ι) ≫ H σ
  have sc : ∀ f ∈ cubeTen x a b c, P f → CTriv w W Rel (fun _ _ g => g (W.ι ≫ f.left)) := fun f hf hP =>
    ctriv_of_sec θ hθ _ (fun y => hW f hf y.2) (fun σ Z r r' h => by
      rw [← Category.assoc, show r' ≫ W.ι = _ from h]
      simp only [Category.assoc, hP σ])
  have s₁ := sc (x * a) (by simp [cubeTen]) (mul hx ha)
  have s₂ := sc (x * a⁻¹) (by simp [cubeTen]) (mul hx (inv ha))
  have s₃ := sc a (by simp [cubeTen]) ha
  have s₄ := sc a⁻¹ (by simp [cubeTen]) (inv ha)
  have s₅ := sc (x * b) (by simp [cubeTen]) (mul hx hb)
  have s₆ := sc (x * c) (by simp [cubeTen]) (mul hx hc)
  have s₇ := sc (x * (b * c)⁻¹) (by simp [cubeTen]) (mul hx (inv (mul hb hc)))
  have s₈ := sc b (by simp [cubeTen]) hb
  have s₉ := sc c (by simp [cubeTen]) hc
  have s₀ := sc (b * c)⁻¹ (by simp [cubeTen]) (inv (mul hb hc))
  have e : CTriv w W Rel (fun _ _ g => g (W.ι ≫ (1 : T ⟶ G).left)) :=
    ((ctriv_of_pmaps (K := PUnit) (fun _ => eSec G) (fun _ => 1) L.rig L.rigGen s
      (fun σ _ => (cubeMapOf (hF σ)).e_comm) hrig).pull (W.ι ≫ T.hom) (Rel' := Rel) (fun σ Z r r' h => by
        show r' ≫ W.ι ≫ T.hom = (r ≫ W.ι ≫ T.hom) ≫ s σ
        rw [← Category.assoc, show r' ≫ W.ι = _ from h]
        simp only [Category.assoc, hH σ])).congr (fun U _ g => by rw [GlobalTheory.UU.one_left]; simp)
  have cu : ∀ u v y : T ⟶ G, P u → P v → P y → CTriv w W Rel (fun _ _ h =>
      h (W.ι ≫ (u * v * y).left) * (h (W.ι ≫ (u * v).left))⁻¹ * (h (W.ι ≫ (u * y).left))⁻¹ *
        (h (W.ι ≫ (v * y).left))⁻¹ * h (W.ι ≫ u.left) * h (W.ι ≫ v.left) *
        h (W.ι ≫ y.left) * (h (W.ι ≫ (1 : T ⟶ G).left))⁻¹) := fun u v y hu hv hy =>
    ((ctriv_of_pmaps (thφ G (x3 G)) thε cb.t cb.isGen (fun σ => (cubeMapOf (hF σ)).F3)
      (fun σ I => (cubeMapOf (hF σ)).psum_comm I.down) hcub).pull (W.ι ≫ (lift u (lift v y)).left) (Rel' := Rel)
      (fun σ Z r r' h => by
        show r' ≫ W.ι ≫ _ = (r ≫ W.ι ≫ _) ≫ _
        rw [← Category.assoc, show r' ≫ W.ι = _ from h]
        simp only [Category.assoc]
        rw [groupPullback_tripleProductMap_lift (cubeMapOf (hF σ)) (H σ) u v y u v y (hu σ) (hv σ) (hy σ)])).congr (fun U _ g => by
      simp only [Category.assoc]
      exact prod_cub u v y (fun ψ => g (W.ι ≫ ψ)))
  have c₁ := cu x a a⁻¹ hx ha (inv ha)
  have c₂ := cu x b c hx hb hc
  have c₃ := cu x (b * c) (b * c)⁻¹ hx (mul hb hc) (inv (mul hb hc))
  have t₂ := ((((c₁.mul s₁).mul s₂).mul s₃.inv).mul s₄.inv)
  have t₃ := (((((((c₂.mul c₃).mul s₅).mul s₆).mul s₇).mul s₈.inv).mul s₉.inv).mul s₀.inv)
  refine ((t₃.mul t₂.inv).mul e).exists_gen L.isLB _ fun U _ g => ?_
  simp only [mul_inv_cancel_right, mul_inv_cancel, _root_.mul_assoc x b c]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Grp

open RigidIsoCube in

theorem pmaps_cub (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I)
    (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
    {s : Sp R ⟶ Sp R} {F : G.left ⟶ G.left} (hF : IsGrpPullback G G s F) (w : LB.Iso U.LG.L (U.LG.L.pull F))
    (hw : w.IsGen) : PMaps w (thφ G (x3 G)) (thφ G (x3 G)) thε U.cubG.t U.cubG.t (cubeMapOf hF).F3 := by
  have hG := GlobalTheory.globalFns_holds
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)
  have pg := (isGen_iff w).1 hw
  let m := cubeMapOf hF
  let e : 𝟙_ (Over (Sp R)) ⟶ G3 G := lift 1 (lift 1 1)
  have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have h1 : (1 : 𝟙_ (Over (Sp R)) ⟶ G).left ≫ m.F = 𝟙 (Sp R) ≫ (1 : Over.mk s ⟶ G).left := by
    rw [GlobalTheory.UU.one_left, GlobalTheory.UU.one_left]
    have : eSec G ≫ m.F = s ≫ eSec G := m.e_comm
    simpa using this
  have heF : e.left ≫ m.F3 = (lift (1 : Over.mk s ⟶ G) (lift (1 : Over.mk s ⟶ G) (1 : Over.mk s ⟶ G))).left :=
    (groupPullback_tripleProductMap_lift m (T := Over.mk s) (𝟙 (Sp R)) 1 1 1 1 1 1 h1 h1 h1).trans (Category.id_comp _)
  have key := pmaps_of_section pg U.LG.isLB U.LG.isLB (φ' := thφ G (x3 G)) (φ := fun k => m.F3 ≫ thφ G (x3 G) k)
    (ε := thε) U.cubG.t U.cubG.isGen (LB.pullGen U.LG.L (thφ G (x3 G)) thε U.cubG.t m.F3)
    (DVR.pullGen_isGen _ _ _ _ U.cubG.isGen _) (fun I => m.psum_comm I.down) _ e.left he sj (fun y J J' hJ hJ' => by
      have p := prod_cub (1 : 𝟙_ (Over (Sp R)) ⟶ G) 1 1 (fun q => gw w q y (J (q ≫ F)) (J' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (val_pull hJ _ _ _).trans ((congrArg (fun q => val (L := U.LG.L) (φ := thφ G (x3 G)) (ε := thε)
        U.cubG.t q y J) heF).trans ?_)
      refine ((isCub_cubV (T := Over.mk s) U.cubG hJ).face 1 1).trans
        (Eq.trans ?_ (congrArg₂ (· * ·) p ((isCub_cubV U.cubG hJ').face 1 1)).symm)
      simp)
  intro Z r z p q hp hq
  refine Eq.trans ?_ (key Z r z p q hp hq)
  rw [Category.comp_id]
  have hm : r z ∈ LB.wchart U.LG.L (fun k => m.F3 ≫ thφ G (x3 G) k) p := Set.mem_iInter.2 fun k => by
    have e₁ : thφ G (x3 G) k ≫ F = m.F3 ≫ thφ G (x3 G) k := m.psum_comm k.down
    show (m.F3 ≫ thφ G (x3 G) k) (r z) ∈ U.LG.L.U (p k)
    rw [← e₁]
    exact hp k
  exact ((gm_res r z _ hm _).trans (gm_pull r m.F3 z (LB.wchart U.LG.L (thφ G (x3 G)) p)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)).symm

theorem exists_sec_of_gen {X : Scheme.{0}} (L : LB X) (W : X.Opens) (t : LB.Gen (L.pull W.ι)) :
    ∃ s : ∀ k, Γ(X, W ⊓ L.U k), ∀ (Z : Scheme.{0}) (r : Z ⟶ W) (z : Z) (k : L.ι), W.ι (r z) ∈ L.U k →
      gs (r ≫ W.ι) z (W ⊓ L.U k) (s k) = (gm r z ((L.pull W.ι).U (fun _ => k)) (t.s (fun _ => k))).val := by
  have le : ∀ k, W.ι ⁻¹ᵁ (W ⊓ L.U k) ≤ (L.pull W.ι).U (fun _ => k) := fun k x hx => mem_pull.2 hx.2
  have hs : ∀ k, Function.Surjective (W.ι.app (W ⊓ L.U k)).hom := fun k => by
    have : IsIso (W.ι.app (W ⊓ L.U k)) := W.ι.isIso_app _ (by simp)
    exact (ConcreteCategory.bijective_of_isIso (W.ι.app (W ⊓ L.U k))).2
  choose s hs using fun k => hs k (res (le k) (t.s (fun _ => k))).val
  refine ⟨s, fun Z r z k hk => ?_⟩
  have hm : W.ι (r z) ∈ W ⊓ L.U k := ⟨(r z).2, hk⟩
  rw [← gs_pull r W.ι z _ hm, hs, gs_unit r z _ hm, gm_res r z _ hm]

end GlobalTheory.Mum.CubeCarried
