import Development.WeilBound.CoreStatements.PadicHodgeComparison.KatzMessingTheorem.QFrobEqSchMap

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison GlobalTheory.LogCris DividedPowers

namespace CompanionTheory.KM.Cris

section General

variable (l : ℕ) [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] (ρ : O →+* k)

def mapId (F : B.Fn O) : B.Fn.Map F F := ⟨𝟙 _, fun h => h⟩

def mapComp {F F' F'' : B.Fn O} (u : B.Fn.Map F F') (v : B.Fn.Map F' F'') : B.Fn.Map F F'' where
  u := u.u ≫ v.u
  ov h := v.ov (u.ov h)

omit [CommRing O] in
theorem map_ext [CommRing O] {F F' : B.Fn O} {u v : B.Fn.Map F F'} (h : u.u = v.u) : u = v := by
  cases u
  cases v
  cases h
  rfl

theorem pullMor_id (F : B.Fn O) (m j : ℕ) (x : CH.H (Wc.OM l F ρ m) j) : (Wc.pullMor l ρ (mapId F) m).pull j x = x := by
  refine (cr_pull_eq (Wc.pullMor l ρ (mapId F) m) (CH.Mor.id _)
    (fun T => crHom (RingHom.id _) (fun _ => rfl) (DPMorphism.id _).isDPMorphism fun h => pt_id _ h _)
    (fun _ _ => rfl) (fun _ _ => rfl) j x).trans ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem limS_id (F : B.Fn O) (j : ℕ) : (Wc.pullS l ρ (mapId F) j).lim = LinearMap.id :=
  LinearMap.ext fun x => Subtype.ext (funext fun m => pullMor_id l ρ F m j (x.1 m))

theorem pullD_id (F : B.Fn O) (j : ℕ) (x : Wc.D l F ρ j) : Wc.pullD l ρ (mapId F) j x = x := by
  unfold Wc.pullD
  rw [limS_id, LinearMap.baseChange_id]
  rfl

omit [Fact l.Prime] [Field k] [CharP k l] [PerfectRing k l] in
theorem schMap_id {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (h : 𝟙 X ≫ q = q) :
    B.schMap (𝟙 X) h = mapId (B.schFn q) := by
  refine map_ext ?_
  ext B₀ y
  exact Category.comp_id y

theorem pullD_schMap_id {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (h : 𝟙 X ≫ q = q) (j : ℕ)
    (x : Wc.D l (B.schFn q) ρ j) : Wc.pullD l ρ (B.schMap (𝟙 X) h) j x = x := by
  rw [schMap_id, pullD_id]

end General

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [Fintype k] [CharP k p]

end CompanionTheory.KM.Cris
