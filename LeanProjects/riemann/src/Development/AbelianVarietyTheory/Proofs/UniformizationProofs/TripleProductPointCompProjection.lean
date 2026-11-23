import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace WCub

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem clause_iff {T XB XG E : Scheme.{0}} {K : Type} [Fintype K] (mB : T ⟶ XB) (mG : T ⟶ XG) (p : K → (T ⟶ E))
    (UB : XB.Opens) (UG : XG.Opens) (W : K → E.Opens) (a : Γ(XB, UB)ˣ) (b : Γ(XG, UG)ˣ) (c : ∀ k, Γ(E, W k)ˣ)
    (ε : K → ℤ) :
    (∀ (V : T.Opens) (hB : V ≤ mB ⁻¹ᵁ UB) (hG : V ≤ mG ⁻¹ᵁ UG) (hw : ∀ k, V ≤ p k ⁻¹ᵁ W k),
      res hB (pullU mB UB a) = (∏ k, res (hw k) (pullU (p k) (W k) (c k)) ^ ε k) * res hG (pullU mG UG b)) ↔
    ∀ y : T, mB y ∈ UB → mG y ∈ UG → (∀ k, p k y ∈ W k) →
      gm mB y UB a = (∏ k, gm (p k) y (W k) (c k) ^ ε k) * gm mG y UG b := by
  have one : ∀ {X : Scheme.{0}} (m : T ⟶ X) (U : X.Opens) (V : T.Opens) (h : V ≤ m ⁻¹ᵁ U) (u : Γ(X, U)ˣ) (y : T),
      y ∈ V → gm (𝟙 T) y V (res h (pullU m U u)) = gm m y U u := fun m U V h u y hy =>
    (gm_res (𝟙 T) y h hy _).trans ((gm_pull (𝟙 T) m y U (h hy) u).trans (by rw [Category.id_comp]))
  have key : ∀ (V : T.Opens) (hG : V ≤ mG ⁻¹ᵁ UG) (hw : ∀ k, V ≤ p k ⁻¹ᵁ W k) (y : T), y ∈ V →
      gm (𝟙 T) y V ((∏ k, res (hw k) (pullU (p k) (W k) (c k)) ^ ε k) * res hG (pullU mG UG b)) =
        (∏ k, gm (p k) y (W k) (c k) ^ ε k) * gm mG y UG b := fun V hG hw y hy =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
      (map_zpow _ _ _).trans (congrArg (· ^ ε k) (one _ _ V _ _ y hy)))) (one _ _ V _ _ y hy))
  constructor
  · intro H y hB hG hw
    let V : T.Opens := mB ⁻¹ᵁ UB ⊓ mG ⁻¹ᵁ UG ⊓ ⟨⋂ k, (p k ⁻¹ᵁ W k : Set T), isOpen_iInter_of_finite fun k =>
      (p k ⁻¹ᵁ W k).isOpen⟩
    have hy : y ∈ V := ⟨⟨hB, hG⟩, Set.mem_iInter.2 hw⟩
    have l : ∀ k, V ≤ p k ⁻¹ᵁ W k := fun k z hz => Set.mem_iInter.1 hz.2 k
    have e := congrArg (gm (𝟙 T) y V) (H V (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) l)
    exact (one _ _ V _ _ y hy).symm.trans (e.trans (key V _ _ y hy))
  · intro H V hB hG hw
    exact unit_ext fun y hy => (one _ _ V _ _ y hy).trans ((H y (hB hy) (hG hy) fun k => hw k hy).trans
      (key V _ _ y hy).symm)

section Cube

variable {S S' : Scheme.{0}} {G : Over S} (f : S' ⟶ S) {E T : Over S'} (p : (Over.map f).obj E ⟶ G)
  (x : Fin 3 → (T ⟶ E))

abbrev tri : T.left ⟶ (G3 G).left :=
  (lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p))).left

theorem tripleProductPoint_comp_projection (i : Fin 3) : tri f p x ≫ (x3 G i).left = (x i).left ≫ p.left := by
  have : lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p)) ≫
      x3 G i = (Over.map f).map (x i) ≫ p := by
    fin_cases i <;> simp [x3]
  exact congrArg (fun q => q.left) this

theorem tri_thφ [GrpObj G] [IsCommMonObj G] [GrpObj E] [IsCommMonObj E] (q : E ⟶ (Over.pullback f).obj G)
    [IsMonHom q] (hp : p.left = q.left ≫ pullback.fst G.hom f) (k : thK) :
    tri f p x ≫ thφ G (x3 G) k = (psum E x k.down).left ≫ p.left := by
  have h := isGrpPullback_pullback G f
  have e₁ := psum_push h (fun i => x i ≫ q) (x3 G)
    (lift ((Over.map f).map (x 0) ≫ p) (lift ((Over.map f).map (x 1) ≫ p) ((Over.map f).map (x 2) ≫ p)))
    (fun i => Over.OverMorphism.ext (by
      refine Eq.trans ?_ (tripleProductPoint_comp_projection f p x i).symm
      rw [hp]
      exact Category.assoc _ _ _)) k.down
  have e₂ := psum_hom (MonoidHom.mk' (fun z : T ⟶ E => z ≫ q) fun a b => MonObj.mul_comp a b q) x k.down
  refine e₁.symm.trans ?_
  rw [hp, ← Category.assoc]
  exact congrArg (fun z => z.left ≫ pullback.fst G.hom f) e₂.symm

end Cube

theorem alg {U K : Type} [CommGroup U] [Fintype K] (ε : K → ℤ) (a b c d : K → U) (h : ∀ k, a k * b k = c k * d k)
    {tM tM' tL tL' : U} (e₁ : tM = (∏ k, a k ^ ε k) * tM') (e₂ : tM = (∏ k, c k ^ ε k) * tL)
    (e₃ : tL = (∏ k, d k ^ ε k) * tL') : tM' = (∏ k, b k ^ ε k) * tL' := by
  have : (∏ k, a k ^ ε k) * (∏ k, b k ^ ε k) = (∏ k, c k ^ ε k) * (∏ k, d k ^ ε k) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [← mul_zpow, ← mul_zpow, h]
  apply mul_left_cancel (a := ∏ k, a k ^ ε k)
  rw [← e₁, e₂, e₃, ← _root_.mul_assoc, ← _root_.mul_assoc, this]

end WCub

open ReciprocityTheory.ChartRestriction.G.Geo.Tor WCub in
set_option maxHeartbeats 1600000 in

theorem w_cub_pull : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain
    R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD
    : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A'
    : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj
    G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc
    : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U
    : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst
    G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf
    φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit)
    (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w'
    : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt'
    e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt'
    e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG
    I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt'
    e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧
    ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst
    D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe
    x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe
    x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I'
    e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL'
    : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e
    G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w'
    e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫
    (fstG I' e G').left) z jL jL')) → ∀ (hgp : Geo.Tor.IsGrpPullback G' G (specOf φ) (bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) (c' : CubicalStr G' L'), Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ
    G (x3 G)) thε c'.t U.cubG.t (Geo.Tor.cubeMapOf hgp).F3 → ∀ (e : ℕ) (T : Over (Spec
    (CommRingCat.of (R' ⧸ I' ^ (e + 1))))) (x : Fin 3 → (T ⟶ thickObj R' I' e G')) (jL
    : thK → L'.L.ι) (jM : thK → D'.toPre.P.L.ι), LB.Coh L'.L (fun k => (lift ((Over.map (thick R' I'
    e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ≫ thφ G' (x3
    G') k) jL → LB.Coh D'.toPre.P.L (fun k => (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt'
    e).pG) (lift ((Over.map (thick R' I' e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map
    (x 2) ≫ (gt' e).pG))).left ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) jM → ∀ (V : T.left.Opens) (hB
    : V ≤ (lift ((Over.map (thick R' I' e)).map (x 0) ≫ (gt' e).pG) (lift ((Over.map (thick R' I'
    e)).map (x 1) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map (x 2) ≫ (gt'
    e).pG))).left ⁻¹ᵁ (Theta D'.toPre.P.A D'.toPre.P.L).U jM) (hG : V ≤ (lift ((Over.map (thick R'
    I' e)).map (x 0) ≫ fstG I' e G') (lift ((Over.map (thick R' I' e)).map (x 1) ≫ fstG I' e G')
    ((Over.map (thick R' I' e)).map (x 2) ≫ fstG I' e G'))).left ⁻¹ᵁ (Theta G' L'.L).U jL) (hw
    : ∀ k : thK, V ≤ (psum (thickObj R' I' e G') x k.down).left ⁻¹ᵁ ((D'.toPre.P.L.pull (gt'
    e).pG.left).U (fun _ => jM k) ⊓ (L'.L.pull (fstG I' e G').left).U
    (fun _ => jL k))), res hB (pullU _ _ (D'.toPre.cub.t.s jM)) = (∏ k : thK, res (hw k) (pullU
    (psum (thickObj R' I' e G') x k.down).left _ ((w' e).s
    (fun _ => jM k, fun _ => jL k))) ^ thε k) * res hG (pullU _ _ (c'.t.s jL)) := by
  intro hG R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ _ U L' wL _ _ _ gt' w' _ _ H hgp c' hc e T x jL' jM' _ cM
  obtain ⟨h, h₁, ⟨h₂, -⟩, sq⟩ := H e
  have hgB := pull_grp hD
  have := (gt' e).q_hom
  have := (U.gt e).q_hom
  have mt : Mono (thick R I e) := by
    have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have mf : Mono (fstG I e G).left := inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))
  have hs : ∀ i, ((x i).left ≫ h ≫ (thickObj R I e G).hom) ≫ thick R I e = T.hom ≫ thick R' I' e ≫ specOf φ := by
    intro i
    have a₁ : (thickObj R I e G).hom ≫ thick R I e = (fstG I e G).left ≫ G.hom := (Over.w (fstG I e G)).symm
    have a₂ : (fstG I' e G').left ≫ G'.hom = (thickObj R' I' e G').hom ≫ thick R' I' e := Over.w (fstG I' e G')
    have a₃ := hgp.1.w
    rw [Category.assoc, Category.assoc, a₁, ← Category.assoc h, h₁, Category.assoc, a₃, ← Category.assoc _ G'.hom, a₂,
      ← Over.w (x i), Category.assoc, Category.assoc]
  let T₀ : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk ((x 0).left ≫ h ≫ (thickObj R I e G).hom)
  let x₀ : Fin 3 → (T₀ ⟶ thickObj R I e G) := fun i => Over.homMk ((x i).left ≫ h) (by
    rw [← cancel_mono (thick R I e)]
    exact ((congrArg (· ≫ thick R I e) (Category.assoc _ _ _)).trans (hs i)).trans (hs 0).symm)
  have f₁ := tri_thφ (thick R' I' e) (fstG I' e G') x (𝟙 _) (Category.id_comp _).symm
  have f₂ := tri_thφ (thick R' I' e) (gt' e).pG x (gt' e).q rfl
  have f₃ := tri_thφ (thick R I e) (fstG I e G) x₀ (𝟙 _) (Category.id_comp _).symm
  have f₄ := tri_thφ (thick R I e) (U.gt e).pG x₀ (U.gt e).q rfl
  have g₁ : tri (thick R' I' e) (fstG I' e G') x ≫ (cubeMapOf hgp).F3 = tri (thick R I e) (fstG I e G) x₀ :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, tripleProductPoint_comp_projection, tripleProductPoint_comp_projection, Category.assoc]
      exact (congrArg ((x i).left ≫ ·) h₁.symm).trans (Category.assoc _ _ _).symm
  have g₂ : tri (thick R' I' e) (gt' e).pG x ≫ (cubeMapOf hgB).F3 = tri (thick R I e) (U.gt e).pG x₀ :=
    hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, tripleProductPoint_comp_projection, tripleProductPoint_comp_projection, Category.assoc]
      exact (congrArg ((x i).left ≫ ·) h₂).trans (Category.assoc _ _ _).symm
  have k₁ : ∀ k : thK, (tri (thick R' I' e) (fstG I' e G') x ≫ thφ G' (x3 G') k) ≫ (cubeMapOf hgp).F =
      tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k := fun k => by
    rw [← g₁, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((cubeMapOf hgp).psum_comm k.down)
  have k₂ : ∀ k : thK, (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F =
      tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k := fun k => by
    rw [← g₂, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) ((cubeMapOf hgB).psum_comm k.down)
  have ph : ∀ k : thK, (psum (thickObj R I e G) x₀ k.down).left = (psum (thickObj R' I' e G') x k.down).left ≫ h :=
    fun k => by
      rw [← cancel_mono (fstG I e G).left]
      refine (f₃ k).symm.trans ((k₁ k).symm.trans ?_)
      rw [f₁ k, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) h₁.symm
  refine (clause_iff (tri (thick R' I' e) (gt' e).pG x) (tri (thick R' I' e) (fstG I' e G') x)
    (fun k : thK => (psum (thickObj R' I' e G') x k.down).left) _ _ _ (D'.toPre.cub.t.s jM') (c'.t.s jL')
    (fun k => (w' e).s (fun _ => jM' k, fun _ => jL' k)) thε).2 fun y hB hL hw => ?_
  obtain ⟨J', hJ', eJ'⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB y _ jM' cM (fun k => Set.mem_iInter.1 hB k)
  choose J hJ using fun χ : T.left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (χ y)
  choose N hN using fun χ : T.left ⟶ G.left => exists_chart U.LG.isLB (χ y)
  let jM : thK → D.toPre.P.L.ι := fun k => J (tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k)
  let jL : thK → U.LG.L.ι := fun k => N (tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k)
  have mM : ∀ k, (tri (thick R I e) (U.gt e).pG x₀ ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k) y ∈ D.toPre.P.L.U (jM k) :=
    fun k => hJ _
  have mL : ∀ k, (tri (thick R I e) (fstG I e G) x₀ ≫ thφ G (x3 G) k) y ∈ U.LG.L.U (jL k) := fun k => hN _
  have e₂ := (clause_iff (tri (thick R I e) (U.gt e).pG x₀) (tri (thick R I e) (fstG I e G) x₀)
    (fun k : thK => (psum (thickObj R I e G) x₀ k.down).left) _ _ _ (D.toPre.cub.t.s jM) (U.cubG.t.s jL)
    (fun k => (U.w e).s (fun _ => jM k, fun _ => jL k)) thε).1
    (U.w_cub e T₀ x₀ jL jM (fun a b e => congrArg N e) (fun a b e => congrArg J e)) y
    (Set.mem_iInter.2 mM) (Set.mem_iInter.2 mL) (fun k => ⟨mem_pull.2 (by
      have := mM k; rw [f₄ k] at this; exact this), mem_pull.2 (by
      have := mL k; rw [f₃ k] at this; exact this)⟩)
  have mL' : ∀ k, ((tri (thick R' I' e) (fstG I' e G') x ≫ thφ G' (x3 G') k) ≫ (cubeMapOf hgp).F) y ∈
      U.LG.L.U (jL k) := fun k => by rw [k₁ k]; exact mL k
  have mM' : ∀ k, ((tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F) y ∈
      D.toPre.P.L.U (jM k) := fun k => by rw [k₂ k]; exact mM k
  have e₃ := hc _ (tri (thick R' I' e) (fstG I' e G') x) y jL jL' mL' (fun k => Set.mem_iInter.1 hL k)
  rw [g₁] at e₃
  have e₁ := cub_pull hG hD (T' := (Over.map (thick R' I' e)).obj T) (z := y) (J := J) (J' := J') hJ hJ'
    ((Over.map (thick R' I' e)).map (x 0) ≫ (gt' e).pG) ((Over.map (thick R' I' e)).map (x 1) ≫ (gt' e).pG)
    ((Over.map (thick R' I' e)).map (x 2) ≫ (gt' e).pG)
  have v₁ : val (L := D.toPre.P.L) (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) D.toPre.cub.t
      (tri (thick R' I' e) (gt' e).pG x ≫ (cubeMapOf hgB).F3) y J =
      gm (tri (thick R I e) (U.gt e).pG x₀) y (LB.wchart _ (thφ D.toPre.P.A (x3 D.toPre.P.A)) jM)
        (D.toPre.cub.t.s jM) := by
    rw [g₂]; rfl
  have v₂ := val_of (L := D'.toPre.P.L) (φ := thφ D'.toPre.P.A (x3 D'.toPre.P.A)) (ε := thε) D'.toPre.cub.t
    (tri (thick R' I' e) (gt' e).pG x) y J' jM' eJ'
  refine alg thε (fun k => gw hD.w ((psum (thickObj R' I' e G') x k.down).left ≫ (gt' e).pG.left) y (jM k) (jM' k))
    (fun k => gw (w' e) (psum (thickObj R' I' e G') x k.down).left y (jM' k) (fun _ => jL' k))
    (fun k => gw (U.w e) ((psum (thickObj R' I' e G') x k.down).left ≫ h) y (jM k) (fun _ => jL k))
    (fun k => gw wL ((psum (thickObj R' I' e G') x k.down).left ≫ (fstG I' e G').left) y (jL k) (jL' k))
    (fun k => sq _ _ y _ _ _ _ ?_ (mem_pull.1 (hw k).1) ?_ (mem_pull.1 (hw k).2))
    (v₁.symm.trans (e₁.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) v₂)))
    (e₂.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) rfl))
    (e₃.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ thε k) ?_) rfl))
  · have := mM' k
    rw [f₂ k] at this
    exact this
  · have := mL' k
    rw [f₁ k] at this
    exact this
  · show gw hD.w (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) y
      (J ((tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k) ≫ (cubeMapOf hgB).F))
      (J' (tri (thick R' I' e) (gt' e).pG x ≫ thφ D'.toPre.P.A (x3 D'.toPre.P.A) k)) = _
    rw [k₂ k, eJ' k, f₂ k]
  · rw [← ph k]; rfl
  · rw [f₁ k]

end GlobalTheory
