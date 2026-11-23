import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCocycleFirstChernClassTateTwist

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.UnitMul
open ClsSpec

variable {R : Type} [CommRing R]

theorem glue_sec (F G : Shv R) (Rel : ∀ U : Scheme.{0}, Sec F U → Sec G U → Prop)
    (hex : ∀ (U : Scheme.{0}) (x : Sec F U), Loc U fun V g => ∃ s, Rel V (Sec.res g x) s)
    (hres : ∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sec F U) (s : Sec G U), Rel U x s → Rel V (Sec.res g x) (Sec.res g s))
    (huniq : ∀ (U : Scheme.{0}) (x : Sec F U) (s s' : Sec G U), Rel U x s → Rel U x s' → s = s') :
    ∃ a : ∀ U : Scheme.{0}, Sec F U → Sec G U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sec F U), Sec.res g (a U x) = a V (Sec.res g x)) ∧
      ∀ (U : Scheme.{0}) (x : Sec F U) (s : Sec G U), Rel U x s → a U x = s := by
  have key : ∀ (U : Scheme.{0}) (x : Sec F U), ∃ a : Sec G U,
      ∀ (V : Scheme.{0}) (g : V ⟶ U) (s : Sec G V), Rel V (Sec.res g x) s → Sec.res g a = s := by
    intro U x
    obtain ⟨S, hS, hP⟩ := hex U x
    choose s hs using hP
    obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue R G U).2 S hS s (fun V W g k hg => by
      refine huniq W (Sec.res (k ≫ g) x) _ _ ?_ (hs _ _ _)
      rw [← res_comp]
      exact hres _ _ _ _ _ (hs _ _ hg))
    refine ⟨a, fun V g s' hs' => sep ⟨S.pullback g, Scheme.etaleTopology.pullback_stable g hS, fun W k hk => ?_⟩⟩
    beta_reduce
    rw [res_comp, ha W (k ≫ g) hk]
    refine huniq W (Sec.res (k ≫ g) x) _ _ (hs _ _ _) ?_
    rw [← res_comp]
    exact hres _ _ _ _ _ hs'
  choose a ha using key
  refine ⟨a, fun V U g x => sep (ClsSpec.loc_mono (hex V (Sec.res g x)) ?_), fun U x s hs => ?_⟩
  · rintro W k ⟨s, hs⟩
    rw [ha V _ W k s hs, res_comp]
    exact ha U x W (k ≫ g) s (by rwa [← res_comp])
  · rw [← res_id (a U x)]
    exact ha U x U (𝟙 U) s (by rwa [res_id])

variable {q : ℕ} [NeZero q] {i k : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
  {D : Cx (ZMod q)} (ι : D ⟶ res _ (tw q i))

def Good (s : ℤ) {U : Scheme.{0}} (b : Sec (D.X s) U) (c : Sec ((res _ (tw q k)).X s) U) : Prop :=
  ∀ (V : Scheme.{0}) (g : V ⟶ U), (∀ ζ : Prim q Γ(V, ⊤),
    Sec.res g c = μ.mul V 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) (Sec.res g b))) ∧
    (Sec.map (ι.f s) (Sec.res g b) = 0 → Sec.res g c = 0)

theorem good_res {s : ℤ} {V U : Scheme.{0}} (g : V ⟶ U) {b : Sec (D.X s) U} {c : Sec ((res _ (tw q k)).X s) U}
    (h : Good μ ι s b c) : Good μ ι s (Sec.res g b) (Sec.res g c) := by
  intro W l
  rw [res_comp, res_comp]
  exact h W (l ≫ g)

theorem good_prim (s : ℤ) {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (b : Sec (D.X s) U) :
    Good μ ι s b (μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b)) := by
  intro V g
  refine ⟨fun ξ => ?_, fun h0 => ?_⟩
  · rw [μ.nat, res_resGen, res_map, resGen_zero_eq ξ (ζ.map g.appTop.hom)]
  · rw [μ.nat, res_map, h0, map_zero]

theorem good_zero (s : ℤ) {U : Scheme.{0}} (b : Sec (D.X s) U) (h : Sec.map (ι.f s) b = 0) : Good μ ι s b 0 := by
  intro V g
  rw [res_zero]
  refine ⟨fun ξ => ?_, fun _ => rfl⟩
  rw [← res_map, h, res_zero, map_zero]

variable {ι} in
theorem localization₂ (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0)
    {s : ℤ} {U : Scheme.{0}} (b : Sec (D.X s) U) :
    Loc U fun V g => Nonempty (Prim q Γ(V, ⊤)) ∨ Sec.map (ι.f s) (Sec.res g b) = 0 := by
  have h1 := (hD s U (Sec.map (ι.f s) b)).1 ⟨b, rfl⟩
  refine ClsSpec.loc_trans (ClsSpec.loc_mono h1 fun V g h => ?_)
  rcases h with hu | h0
  · exact ClsSpec.loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity q V).1 hu) fun W l ⟨ζ⟩ => Or.inl ⟨ζ⟩
  · rw [res_map] at h0
    exact GlobalTheory.T.etaleLocal_property_calculus_rules.1 V _ fun W l => Or.inr (by rw [← res_comp, ← res_map, h0, res_zero])

end GlobalTheory.EtC.UnitMul

namespace GlobalTheory.EtC.UnitMul
open ClsSpec

variable {R : Type} [CommRing R]

variable {q : ℕ} [NeZero q] {i k : ℤ} (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
  {D : Cx (ZMod q)} (ι : D ⟶ res _ (tw q i))

theorem res_smul {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (r : ULift.{1} R) (a : Sec F U) :
    Sec.res g (r • a) = r • Sec.res g a := map_smul _ _ _
theorem smap_smul {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (r : ULift.{1} R) (a : Sec F U) :
    Sec.map φ (r • a) = r • Sec.map φ a := map_smul _ _ _

variable {ι} in
theorem good_uniq (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0)
    {s : ℤ} {U : Scheme.{0}} (b : Sec (D.X s) U) (c c' : Sec ((res _ (tw q k)).X s) U)
    (hc : Good μ ι s b c) (hc' : Good μ ι s b c') : c = c' :=
  sep (ClsSpec.loc_mono (localization₂ hD b) fun V g h => h.elim (fun ⟨ζ⟩ => ((hc V g).1 ζ).trans ((hc' V g).1 ζ).symm)
    (fun h0 => ((hc V g).2 h0).trans ((hc' V g).2 h0).symm))

variable {ι} in

theorem exists_fam (hD : ∀ n U (a : Sec ((res _ (tw q i)).X n) U), (∃ b, Sec.map (ι.f n) b = a) ↔
      Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) (s : ℤ) :
    ∃ a : ∀ U : Scheme.{0}, Sec (D.X s) U → Sec ((res _ (tw q k)).X s) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) (x : Sec (D.X s) U), Sec.res g (a U x) = a V (Sec.res g x)) ∧
      ∀ (U : Scheme.{0}) (x : Sec (D.X s) U) (c : Sec ((res _ (tw q k)).X s) U), Good μ ι s x c → a U x = c :=
  glue_sec _ _ (fun U x c => Good μ ι s x c)
    (fun U x => ClsSpec.loc_mono (localization₂ hD x) fun V g h => h.elim (fun ⟨ζ⟩ => ⟨_, good_prim μ ι s ζ _⟩)
      (fun h0 => ⟨0, good_zero μ ι s _ h0⟩))
    (fun V U g x c h => good_res μ ι g h)
    (fun U x c c' h h' => good_uniq μ hD x c c' h h')

end GlobalTheory.EtC.UnitMul

open GlobalTheory.EtC.UnitMul ClsSpec in

theorem GlobalTheory.EtC.unit_mul_chain_map : ∀ (q : ℕ) [NeZero q] (i k : ℤ) (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q k)))
    (D : Cx (ZMod q)) (ι : D ⟶ res _ (tw q i)), (∀ n U (a : Sec ((res _ (tw q i)).X n) U),
      (∃ b, Sec.map (ι.f n) b = a) ↔ Loc U fun V g => IsUnit (q : Γ(V, ⊤)) ∨ Sec.res g a = 0) →
    ∃ u : D ⟶ res _ (tw q k), ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (s : ℤ) (b : Sec (D.X s) U),
      Sec.map (u.f s) b = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) b) := by
  intro q _ i k μ D ι hD
  choose a ha hs using exists_fam μ hD
  have aP : ∀ (s : ℤ) (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)) (x : Sec (D.X s) U),
      a s U x = μ.mul U 0 s s (zero_add s) (resGen 0 ζ) (Sec.map (ι.f s) x) :=
    fun s U ζ x => hs s U x _ (good_prim μ ι s ζ x)
  have aZ : ∀ (s : ℤ) (U : Scheme.{0}) (x : Sec (D.X s) U), Sec.map (ι.f s) x = 0 → a s U x = 0 :=
    fun s U x h => hs s U x 0 (good_zero μ ι s x h)
  have aAdd : ∀ (s : ℤ) (U : Scheme.{0}) (x y : Sec (D.X s) U), a s U (x + y) = a s U x + a s U y := by
    intro s U x y
    refine sep (ClsSpec.loc_mono (ClsSpec.loc_and (localization₂ hD x) (localization₂ hD y)) fun V g h => ?_)
    rw [res_add, ha, ha, ha, res_add]
    rcases h with ⟨⟨⟨ζ⟩⟩ | hx, ⟨⟨ζ⟩⟩ | hy⟩
    · rw [aP s V ζ, aP s V ζ, aP s V ζ, smap_add, map_add]
    · rw [aP s V ζ, aP s V ζ, aP s V ζ, smap_add, map_add]
    · rw [aP s V ζ, aP s V ζ, aP s V ζ, smap_add, map_add]
    · rw [aZ s V _ hx, aZ s V _ hy, aZ s V _ (by rw [smap_add, hx, hy, add_zero]), add_zero]
  have aSmul : ∀ (s : ℤ) (U : Scheme.{0}) (r : ULift.{1} (ZMod q)) (x : Sec (D.X s) U), a s U (r • x) = r • a s U x := by
    intro s U r x
    refine sep (ClsSpec.loc_mono (localization₂ hD x) fun V g h => ?_)
    rw [res_smul, ha, ha, res_smul]
    rcases h with ⟨⟨ζ⟩⟩ | hx
    · rw [aP s V ζ, aP s V ζ, smap_smul, map_smul]
    · rw [aZ s V _ hx, aZ s V _ (by rw [smap_smul, hx, smul_zero]), smul_zero]
  have aD : ∀ (s : ℤ) (U : Scheme.{0}) (x : Sec (D.X s) U),
      Sec.map ((res _ (tw q k)).d s (s + 1)) (a s U x) = a (s + 1) U (Sec.map (D.d s (s + 1)) x) := by
    intro s U x
    have hι : ∀ {V : Scheme.{0}} (y : Sec (D.X s) V), Sec.map ((res _ (tw q i)).d s (s + 1)) (Sec.map (ι.f s) y) =
        Sec.map (ι.f (s + 1)) (Sec.map (D.d s (s + 1)) y) := fun y => by
      rw [map_comp, ι.comm, ← map_comp]
    refine sep (ClsSpec.loc_mono (localization₂ hD x) fun V g h => ?_)
    rw [res_map, ha, ha, res_map]
    rcases h with ⟨⟨ζ⟩⟩ | hx
    · rw [aP s V ζ, aP (s + 1) V ζ, μ.leibniz, ← hι]
      have h0 : Sec.map ((res _ (tw q 0)).d 0 (0 + 1)) (resGen 0 ζ) = 0 := d_resGen 0 ζ
      rw [h0, map_zero, LinearMap.zero_apply, zero_add, Int.negOnePow_zero, one_smul]
    · rw [aZ s V _ hx, smap_zero, aZ (s + 1) V _ (by rw [← hι, hx, smap_zero])]
  let F : ∀ s : ℤ, D.X s ⟶ (res _ (tw q k)).X s := fun s =>
    ⟨{ app := fun X => ModuleCat.ofHom
          { toFun := a s X.unop
            map_add' := aAdd s X.unop
            map_smul' := aSmul s X.unop }
       naturality := fun X Y f => by
          apply ModuleCat.hom_ext; apply LinearMap.ext; intro x
          exact (ha s Y.unop X.unop f.unop x).symm }⟩
  refine ⟨{ f := F, comm' := fun s t hst => ?_ }, fun U ζ s b => aP s U ζ b⟩
  change s + 1 = t at hst
  subst hst
  apply Sheaf.hom_ext; ext X x
  exact aD s X.unop x
