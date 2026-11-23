import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.SameB

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.ToChart

theorem gm_res_pull {X Y : Scheme.{0}} (g : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ g ⁻¹ᵁ U) {y : Y} (hy : y ∈ V)
    (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res h (pullU g U a)) = gm g y U a :=
  (gm_res _ y h hy _).trans ((gm_pull (𝟙 Y) g y U (h hy) a).trans (by rw [Category.id_comp]))

theorem cub_alg' {M : Type} [CommGroup M] {C C' a b c d e g h k : M} (H : C * b * c * d * k = a * e * g * h * C') :
    C = a * b⁻¹ * c⁻¹ * d⁻¹ * e * g * h * k⁻¹ * C' := by
  apply Additive.ofMul.injective
  have H' := congrArg Additive.ofMul H
  simp only [ofMul_mul, ofMul_inv] at H' ⊢
  linear_combination (norm := abel) H'

theorem cube_left {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {T : Over S} {T' : Over S'} (β : (T' ⟶ G') →* (T ⟶ G)) (x : Fin 3 → (T' ⟶ G')) (k : thK) :
    (lift (β (x 0)) (lift (β (x 1)) (β (x 2)))).left ≫ thφ G (x3 G) k = (β (psum G' x k.down)).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom (lift (β (x 0)) (lift (β (x 1)) (β (x 2))))) (x3 G) k.down).trans
    ((congrArg (fun q => psum G q k.down) (funext fun i => by fin_cases i <;> simp [preHom, x3])).trans
      (psum_hom β x k.down).symm))

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (e : ℕ)

def fstHom (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ fstG I e G) fun x y =>
    toBase_mul_pullback G (thick R I e) T x y

variable {I e} {D : DegPre R} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def projHom (g : GtCoord I D e G) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ D.P.A) :=
  MonoidHom.mk' (fun x => (Over.map (thick R I e)).map x ≫ g.pG) fun x y => by
    have := g.q_hom
    have h : ∀ a : T ⟶ thickObj R I e G, (Over.map (thick R I e)).map a ≫ g.pG = fstHom I e D.P.A T (a ≫ g.q) :=
      fun a => by rw [← Category.assoc, ← Functor.map_comp]; rfl
    rw [h, h, h, MonObj.mul_comp, map_mul]

variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} (U : PreU I D A G)

theorem w_compat (e : ℕ) (p : (PUnit → D.P.L.ι) × (PUnit → U.P.L.L.ι))
    (V : (thickObj R I e G).left.Opens)
    (h₁ : V ≤ thickMap R I e G ⁻¹ᵁ ((D.P.L.pull (U.gt (e + 1)).pG.left).U p.1 ⊓
      (U.P.L.L.pull (fstG I (e + 1) G).left).U p.2))
    (h₂ : V ≤ (D.P.L.pull (U.gt e).pG.left).U p.1 ⊓ (U.P.L.L.pull (fstG I e G).left).U p.2) :
    res h₁ (pullU (thickMap R I e G) _ ((U.w (e + 1)).s p)) = res h₂ ((U.w e).s p) := by
  refine unit_ext fun y hy => ?_
  have := U.w_compat e _ (𝟙 _) y (p.1 PUnit.unit) (p.2 PUnit.unit) (mem_pull.1 (h₂ hy).1) (mem_pull.1 (h₂ hy).2)
  rw [Category.id_comp] at this
  exact (gm_res_pull _ h₁ hy _).trans (this.trans (gm_res _ y h₂ hy _).symm)

theorem w_rig (e : ℕ) (p : (PUnit → D.P.L.ι) × (PUnit → U.P.L.L.ι))
    (V : (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))).Opens)
    (h₁ : V ≤ eSec (thickObj R I e G) ⁻¹ᵁ
      ((D.P.L.pull (U.gt e).pG.left).U p.1 ⊓ (U.P.L.L.pull (fstG I e G).left).U p.2))
    (h₂ : V ≤ thick R I e ⁻¹ᵁ (U.P.L.L.pull (eSec G)).U p.2)
    (h₃ : V ≤ thick R I e ⁻¹ᵁ (D.P.L.pull (eSec D.P.A)).U p.1) :
    res h₁ (pullU (eSec (thickObj R I e G)) _ ((U.w e).s p)) *
      res h₂ (pullU (thick R I e) _ (U.P.L.rig.s p.2)) =
      res h₃ (pullU (thick R I e) _ (D.rig.s p.1)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y (K := Fin 2)
    ![thick R I e ≫ eSec G, eSec (thickObj R I e G) ≫ (fstG I e G).left] (fun _ => p.2 PUnit.unit) (fun _ _ _ => rfl)
    (Fin.forall_fin_two.2 ⟨Set.mem_iInter.1 (h₂ hy) PUnit.unit, Set.mem_iInter.1 (h₁ hy).2 PUnit.unit⟩)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y (K := Fin 2)
    ![thick R I e ≫ eSec D.P.A, eSec (thickObj R I e G) ≫ (U.gt e).pG.left] (fun _ => p.1 PUnit.unit) (fun _ _ _ => rfl)
    (Fin.forall_fin_two.2 ⟨Set.mem_iInter.1 (h₃ hy) PUnit.unit, Set.mem_iInter.1 (h₁ hy).1 PUnit.unit⟩)
  have H := (U.w_vals e (𝟙_ _) y JG J hJG hJ _ (fun _ => rfl)).1
  have o : (1 : 𝟙_ _ ⟶ thickObj R I e G).left = eSec (thickObj R I e G) :=
    (one_left _ _).trans (Category.id_comp _)
  have t : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).hom ≫ thick R I e = thick R I e := Category.id_comp _
  rw [o, t] at H
  have a := val_of (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (thick R I e) y J p.1
    (fun _ => eB 0)
  have b := val_of (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (thick R I e) y JG p.2
    (fun _ => eG 0)
  have c := congrArg₂ (fun j k => gw (U.w e) (eSec (thickObj R I e G)) y j (fun _ => k)) (eB 1) (eG 1)
  refine (map_mul _ _ _).trans (Eq.trans ?_ (gm_res_pull _ h₃ hy _).symm)
  refine (congrArg₂ (· * ·) (gm_res_pull _ h₁ hy _) (gm_res_pull _ h₂ hy _)).trans ?_
  exact (a.symm.trans (H.trans (congrArg₂ (· * ·) c b))).symm

theorem w_even (e : ℕ) (jS : Fin 2 → U.P.L.L.ι) (jT : Fin 2 → D.P.L.ι)
    (cS : LB.Coh U.P.L.L (fun k => (fstG I e G).left ≫ (![(ι[G]).left, 𝟙 G.left] : Fin 2 → _) k) jS)
    (cT : LB.Coh D.P.L
      (fun k => (U.gt e).pG.left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k) jT)
    (V : (thickObj R I e G).left.Opens)
      (h₁ : V ≤ (U.gt e).pG.left ⁻¹ᵁ (LB.LinComb D.P.L (K := Fin 2)
        ![(ι[D.P.A]).left, 𝟙 D.P.A.left] ![1, -1]).U jT)
      (h₂ : V ≤ (D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 1) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 1))
      (h₃ : V ≤ (ι[thickObj R I e G]).left ⁻¹ᵁ ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jT 0) ⊓
        (U.P.L.L.pull (fstG I e G).left).U (fun _ => jS 0)))
      (h₄ : V ≤ (fstG I e G).left ⁻¹ᵁ (LB.LinComb U.P.L.L (K := Fin 2)
        ![(ι[G]).left, 𝟙 G.left] ![1, -1]).U jS) :
      res h₁ (pullU (U.gt e).pG.left _ (D.sym.s jT)) *
        res h₂ ((U.w e).s (fun _ => jT 1, fun _ => jS 1)) =
      res h₃ (pullU (ι[thickObj R I e G]).left _ ((U.w e).s (fun _ => jT 0, fun _ => jS 0))) *
        res h₄ (pullU (fstG I e G).left _ (U.P.sym.s jS)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y _ jS cS (fun k => Set.mem_iInter.1 (h₄ hy) k)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y _ jT cT (fun k => Set.mem_iInter.1 (h₁ hy) k)
  have H := (U.w_vals e _ y JG J hJG hJ _ (fun _ => rfl)).2.1 (𝟙 _)
  have o : ((𝟙 (thickObj R I e G))⁻¹).left = (ι[thickObj R I e G]).left := by rw [Hom.inv_def, Category.id_comp]
  have iG : ((𝟙 (thickObj R I e G))⁻¹).left ≫ (fstG I e G).left = (fstG I e G).left ≫ (ι[G]).left :=
    (congrArg (fun q => q.left) (map_inv (fstHom I e G _) (𝟙 _))).trans
      (congrArg (· ≫ (ι[G]).left) (Category.id_comp (fstG I e G).left))
  have iB : ((𝟙 (thickObj R I e G))⁻¹).left ≫ (U.gt e).pG.left = (U.gt e).pG.left ≫ (ι[D.P.A]).left :=
    (congrArg (fun q => q.left) (map_inv (projHom (U.gt e) _) (𝟙 _))).trans
      (congrArg (· ≫ (ι[D.P.A]).left) (Category.id_comp (U.gt e).pG.left))
  have g₀ : JG ((fstG I e G).left ≫ (ι[G]).left) = jS 0 := eG 0
  have g₁ : JG (fstG I e G).left = jS 1 := (congrArg JG (Category.comp_id _).symm).trans (eG 1)
  have b₀ : J ((U.gt e).pG.left ≫ (ι[D.P.A]).left) = jT 0 := eB 0
  have b₁ : J (U.gt e).pG.left = jT 1 := (congrArg J (Category.comp_id _).symm).trans (eB 1)
  rw [iG, iB, o, g₀, b₀, Over.id_left, Category.id_comp, Category.id_comp, g₁, b₁, val_of _ _ _ _ jT eB,
    val_of _ _ _ _ jS eG] at H
  refine (map_mul _ _ _).trans (Eq.trans ?_ (map_mul _ _ _).symm)
  exact (congrArg₂ (· * ·) (gm_res_pull _ h₁ hy _) (gm_res _ y h₂ hy _)).trans
    (H.trans (congrArg₂ (· * ·) (gm_res_pull _ h₃ hy _) (gm_res_pull _ h₄ hy _)).symm)

theorem w_cub (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))
    (x : Fin 3 → (T ⟶ thickObj R I e G)) (jL : thK → U.P.L.L.ι) (jM : thK → D.P.L.ι)
    (cL : LB.Coh U.P.L.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
        ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ≫ thφ G (x3 G) k) jL)
    (cM : LB.Coh D.P.L (fun k => (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
      (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
        ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ≫
          thφ D.P.A (x3 D.P.A) k) jM)
    (V : T.left.Opens)
      (hB : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ (U.gt e).pG)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ (U.gt e).pG)
          ((Over.map (thick R I e)).map (x 2) ≫ (U.gt e).pG))).left ⁻¹ᵁ
            (Theta D.P.A D.P.L).U jM)
      (hG : V ≤ (lift ((Over.map (thick R I e)).map (x 0) ≫ fstG I e G)
        (lift ((Over.map (thick R I e)).map (x 1) ≫ fstG I e G)
          ((Over.map (thick R I e)).map (x 2) ≫ fstG I e G))).left ⁻¹ᵁ (Theta G U.P.L.L).U jL)
      (hw : ∀ k : thK, V ≤ (psum (thickObj R I e G) x k.down).left ⁻¹ᵁ
        ((D.P.L.pull (U.gt e).pG.left).U (fun _ => jM k) ⊓
          (U.P.L.L.pull (fstG I e G).left).U (fun _ => jL k))) :
      res hB (pullU _ _ (D.cub.t.s jM)) =
        (∏ k : thK, res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
          ((U.w e).s (fun _ => jM k, fun _ => jL k))) ^ thε k) *
        res hG (pullU _ _ (U.P.c.t.s jL)) := by
  refine unit_ext fun y hy => ?_
  obtain ⟨JG, hJG, eG⟩ := exists_good U.P.L.L U.P.L.isLB y _ jL cL (fun k => Set.mem_iInter.1 (hG hy) k)
  obtain ⟨J, hJ, eB⟩ := exists_good D.P.L D.P.isLB y _ jM cM (fun k => Set.mem_iInter.1 (hB hy) k)
  obtain ⟨h, hh⟩ : ∃ h : (T.left ⟶ (thickObj R I e G).left) → (T.left.presheaf.stalk y)ˣ, ∀ q,
      h q = gw (U.w e) q y (J (q ≫ (U.gt e).pG.left)) (fun _ => JG (q ≫ (fstG I e G).left)) := ⟨_, fun _ => rfl⟩
  have H := (U.w_vals e T y JG J hJG hJ (fun a => h a.left) (fun _ => hh _)).2.2 (x 0) (x 1) (x 2)
  have P := prod_cub (x 0) (x 1) (x 2) h
  have Q : ∀ k : thK, gm (𝟙 T.left) y V (res (hw k) (pullU (psum (thickObj R I e G) x k.down).left _
      ((U.w e).s (fun _ => jM k, fun _ => jL k)))) =
      h ((lift (x 0) (lift (x 1) (x 2))).left ≫ thφ (thickObj R I e G) (x3 _) k) := fun k => by
    have g : JG ((psum (thickObj R I e G) x k.down).left ≫ (fstG I e G).left) = jL k :=
      (congrArg JG (cube_left (fstHom I e G T) x k).symm).trans (eG k)
    have b : J ((psum (thickObj R I e G) x k.down).left ≫ (U.gt e).pG.left) = jM k :=
      (congrArg J (cube_left (projHom (U.gt e) T) x k).symm).trans (eB k)
    refine (gm_res_pull _ (hw k) hy _).trans (Eq.trans ?_ (congrArg h (cube_left (MonoidHom.id _) x k)).symm)
    exact ((hh _).trans (congrArg₂ (fun j l => gw (U.w e) (psum (thickObj R I e G) x k.down).left y j (fun _ => l))
      b g)).symm
  have a := val_of (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t _ y J jM eB
  have b := val_of (L := U.P.L.L) (φ := thφ G (x3 G)) (ε := thε) U.P.c.t _ y JG jL eG
  refine (gm_res_pull _ hB hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans
      (congrArg (· ^ thε k) (Q k)))).trans P) (gm_res_pull _ hG hy _))).symm)
  exact a.symm.trans ((cub_alg' H).trans (congrArg₂ (· * ·) rfl b))

theorem exists_match : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D.toPre A G), ∃ U' : UnifPre I D A G, Match U U' :=
  fun _ _ _ _ _ _ _ _ _ U =>
    ⟨{ smooth := U.semi.smooth
       separated := U.semi.separated
       gen := U.gen
       gen_hom := U.gen_hom
       LG := U.P.L
       cubG := U.P.c
       symG := U.P.sym
       symG_gen := U.P.sym_gen
       symG_rig := U.P.sym_rig
       ext := ⟨U.wA, U.wA_gen⟩
       gt := U.gt
       gt_q := U.gt_q
       gt_t := U.gt_t
       w := U.w
       w_gen := U.w_gen
       w_rig := w_rig U
       w_even := w_even U
       w_cub := w_cub U
       w_compat := w_compat U }, ⟨rfl, rfl, HEq.rfl, HEq.rfl, rfl, HEq.rfl⟩⟩

end GlobalTheory.UU.ToChart
end
