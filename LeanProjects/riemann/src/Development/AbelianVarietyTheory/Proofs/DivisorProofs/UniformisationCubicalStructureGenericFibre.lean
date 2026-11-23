import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkZeta
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumFConstMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefTwistPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HRedFst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsoVal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericCube

theorem exists_iso_section {X H Y : Scheme.{0}} {L : LB X} {M : LB H} {f : Y ⟶ H} {ψ : Y ⟶ X} (g : H ⟶ Y)
    (hg : g ≫ f = 𝟙 H) (w : LB.Iso (M.pull f) (L.pull ψ)) (hw : w.IsGen) :
    ∃ w' : LB.Iso M (L.pull (g ≫ ψ)), w'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) := by
  have mm : ∀ (y : H) (k : M.ι), y ∈ M.U k → g y ∈ (M.pull f).U (fun _ => k) := fun y k hy => mem_pull.2 (by
    have e : (g ≫ f) y = y := by rw [hg]; rfl
    exact (congrArg (· ∈ M.U k) e).mpr hy)
  have le : ∀ (j : L.ι) (k : M.ι), (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k ≤
      g ⁻¹ᵁ ((L.pull ψ).U (fun _ => j) ⊓ (M.pull f).U (fun _ => k)) := fun j k y hy =>
    ⟨mem_pull.2 (mem_pull₂.1 hy.1), mm y k hy.2⟩
  let w' : LB.Iso M (L.pull (g ≫ ψ)) :=
    ⟨fun p => res (le (p.1 PUnit.unit) p.2) (pullU g _ (w.s (fun _ => p.1 PUnit.unit, fun _ => p.2)))⟩
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) (j : L.ι) (k : M.ι),
      ψ (g (r z)) ∈ L.U j → r z ∈ M.U k → Geo.Tor.gw w' r z j k = Geo.Tor.gw w (r ≫ g) z j (fun _ => k) :=
    fun Z r z j k hj hk => by
      have m : r z ∈ (L.pull (g ≫ ψ)).U (fun _ => j) ⊓ M.U k := ⟨mem_pull₂.2 hj, hk⟩
      exact (gm_res r z (le j k) m _).trans (gm_pull r g z _ (le j k m) _)
  refine ⟨w', (isGen_iff w').2 fun Z r z j j' k k' hj hj' hk hk' => ?_, hv⟩
  have e := (isGen_iff w).1 hw Z (r ≫ g) z j j' (fun _ => k) (fun _ => k') hj hj' (mm _ k hk) (mm _ k' hk')
  rw [Geo.Tor.gm_pull_g M f (r ≫ g) z _ _ (mm _ k hk) (mm _ k' hk'), Category.assoc r g f, hg, Category.comp_id,
    Category.assoc] at e
  rw [hv Z r z j k hj hk, hv Z r z j' k' hj' hk']
  exact e

theorem cube_through_iso : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (h : Finset (Fin 3) → ((𝟙_ (Over (Sp V))) ⟶ G)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → h ∅ = 1 → h {0, 1} = h {0} * h {1} → h {0, 2} = h {0} * h {2} → h {1, 2} = h {1} * h {2} → h {0, 1, 2} = h {0} * h {1} * h {2} → (∀ S, IntTerm.Ext U.toUnifPre (x S) (h S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JG : ((TF (R := V) (FractionRing V)).left ⟶ G.left) → U.LG.L.ι), Good A.L z JA → Good U.LG.L z JG → (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1, 2}).left) (fun _ => JA (x {0, 1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}).left) (fun _ => JA (x {0}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}).left) (fun _ => JA (x {1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}).left) (fun _ => JA (x {2}).left)) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) = cubV U.cubG z JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1}) ((toUnit (TF (R := V) (FractionRing V))) ≫ h {2}) * (Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 1}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 1}).left) (fun _ => JA (x {0, 1}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {0, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {0, 2}).left) (fun _ => JA (x {0, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x {1, 2}).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h {1, 2}).left) (fun _ => JA (x {1, 2}).left) * Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x ∅).left ≫ U.gen.inv.left) z (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h ∅).left) (fun _ => JA (x ∅).left)) := by
  intro V _ _ _ _ D A G _ _ _ U w₀ hw₀ ρ hρ c x h x0 x01 x02 x12 x012 h0 h01 h02 h12 h012 hE z JA JG hJA hJG
  haveI := U.gen_hom
  haveI : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK V) (U.gen.inv.left ≫ pullback.fst G.hom (jK V)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr (Category.id_comp _) rfl
  obtain ⟨w, hw, hv⟩ := exists_iso_section U.gen.inv.left (congrArg (fun q => q.left) U.gen.inv_hom_id) w₀ hw₀
  have e := cub_w U.cubG c GlobalTheory.abelianSchemeLaws_all.1.globalFns A.isAb gp w hw
    (s' := jFK (R := V) (FractionRing V)) (s := jFK (R := V) (FractionRing V) ≫ jK V) (z := z) hJG hJA
    (x {0}) (x {1}) (x {2}) _ _ _ (hE {0}) (hE {1}) (hE {2})
  have k : ∀ S, Om w (s' := jFK (R := V) (FractionRing V)) z JG JA (x S) =
      Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
        (JG ((toUnit (TF (R := V) (FractionRing V))) ≫ h S).left) (fun _ => JA (x S).left) := fun S => by
    refine (hv _ (x S).left z _ _ (hJG ((x S).left ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK V))) (hJA _)).trans ?_
    exact congrArg (fun q => Geo.Tor.gw (Y := (TF (R := V) (FractionRing V)).left) w₀ ((x S).left ≫ U.gen.inv.left) z
      (JG q) (fun _ => JA (x S).left)) (hE S)
  rw [← x012, ← x01, ← x02, ← x12, ← x0, k, k, k, k, k, k, k, k] at e
  refine Eq.trans ?_ (congrArg (· * _) e.symm)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, id]
  abel

end GlobalTheory.GenericCube
