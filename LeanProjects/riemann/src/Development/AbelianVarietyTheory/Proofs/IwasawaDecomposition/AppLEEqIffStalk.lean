import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtBC

theorem appLE_eq_iff_stalk {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
    {V : X.Opens} (hV : ∀ y, F y ∈ V) (s : ∀ j, Γ(X, V ⊓ L.U j)) (s' : L'.Sec) :
    (∀ (j : (L.pull F).ι) (i : L'.ι) (hle : (L.pull F).U j ⊓ L'.U i ≤ F ⁻¹ᵁ (V ⊓ L.U (j PUnit.unit))),
      (F.appLE _ _ hle).hom (s (j PUnit.unit)) =
        (show Γ(X', (L.pull F).U j ⊓ L'.U i) from (w.s (j, i)).val) * resG _ inf_le_right (s'.f i)) ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) j k, F (r z) ∈ L.U j → r z ∈ L'.U k →
      gs (r ≫ F) z _ (s j) = (gw w r z j k).val * gs r z _ (s'.f k) := by
  constructor
  · intro h Z r z j k hj hk
    have hy : r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k := ⟨mem_pull.2 hj, hk⟩
    have hle : (L.pull F).U (fun _ => j) ⊓ L'.U k ≤ F ⁻¹ᵁ (V ⊓ L.U j) := fun y hy => ⟨hV y, mem_pull.1 hy.1⟩
    refine (gs_appLE F _ _ hle r z hy _).symm.trans ((congrArg (gs r z _) (h (fun _ => j) k hle)).trans ?_)
    rw [gs_mul _ z _ hy, gs_res _ z _ hy]
    exact congrArg (· * _) (gs_unit _ z _ hy _)
  · intro h j i hle
    refine fn_ext fun y hy => ?_
    refine (gs_appLE F _ _ hle (𝟙 _) y hy _).trans ((h _ (𝟙 _) y _ i (mem_pull.1 hy.1) hy.2).trans ?_)
    rw [gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg (· * _) (gs_unit _ y _ hy _).symm

theorem mem_of_comm {X X' T T' : Scheme.{0}} {F : X' ⟶ X} {π : X ⟶ T} {π' : X' ⟶ T'} {z : T' ⟶ T}
    (e : F ≫ π = π' ≫ z) {U : T.Opens} (hz : ⊤ ≤ z ⁻¹ᵁ U) (y : X') : F y ∈ π ⁻¹ᵁ U := by
  show π (F y) ∈ U
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  exact hz (Set.mem_univ _)

theorem spMap_comp₀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (f' : R' →+* R'') :
    spMap (f'.comp f) = spMap f' ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {M : GChart Y} {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {z : Sp R ⟶ Y.X} {hz : ⊤ ≤ z ⁻¹ᵁ M.U}
  {x : KeyIn R} {x' : KeyIn R'}

theorem keyAt_of_keyPB (h : KeyAt M z hz x) (h' : KeyPB x' x f) :
    KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x' := by
  obtain ⟨φ, he, w, hg, hp, hw, hr, hs, hv⟩ := h
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := h'
  have g := (isGen_iff w).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp x.P.isLB w w' g g' Y.t.PP.isLB x'.P.isLB
  have he'' : eSec x'.P.A ≫ φ' ≫ φ = (spMap f ≫ z) ≫ eSec Y.t.G := by
    rw [← Category.assoc, he', Category.assoc, he, Category.assoc]
  have hF : F' = dualMap f := KeyCancel.dualNumber_ringHom_ext
    (fun a => by
      rw [hF']
      ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])
    (by
      rw [hε']
      ext <;> simp [dualMap])
  have hq := hp'.comp hp
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, hq, (isGen_iff w'').2 (T.pgen_comp x.P.isLB g g'), ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _
      (rigPull_le φ z he Y.t.PP.L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _
      (rigPull_le φ' (spMap f) he' x.P.L) (fun _ => rfl)).1 hr'
    exact (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
      (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).2
      (T.pmaps_comp x.P.isLB (fun _ => he') r₀ r₁)
  · refine (appLE_eq_iff_stalk w'' (mem_of_comm hq.1.w (le_preimage_comp _ hz)) M.θ x'.th).2
      fun Z q y j k hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart x.P.isLB (φ' (q y))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.1.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).1 hs' Z q y i k hi hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [← Category.assoc, hv', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
      hF, Category.assoc]
    rfl

theorem keyPB_of_keyAt (h : KeyAt M z hz x) (h' : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x') :
    KeyPB x' x f := by
  obtain ⟨φ, he, w, hg, hc, hw, hr, hs, hv⟩ := h
  obtain ⟨φ'', he'', w'', hg'', hc'', hw'', hr'', hs'', hv''⟩ := h'
  have hp := hc.1
  obtain ⟨φ', hφ, hw0⟩ : ∃ φ' : x'.P.A.left ⟶ x.P.A.left, φ' ≫ φ = φ'' ∧
      φ' ≫ x.P.A.hom = x'.P.A.hom ≫ spMap f :=
    ⟨hp.lift φ'' (x'.P.A.hom ≫ spMap f) (by rw [hc''.1.w, Category.assoc]), hp.lift_fst _ _ _,
      hp.lift_snd _ _ _⟩
  subst hφ
  have he' : eSec x'.P.A ≫ φ' = spMap f ≫ eSec x.P.A := by
    apply hp.hom_ext
    · rw [Category.assoc, he'', Category.assoc, Category.assoc, he]
    · have a₁ : eSec x'.P.A ≫ x'.P.A.hom = 𝟙 _ := Over.w η[x'.P.A]
      have a₂ : eSec x.P.A ≫ x.P.A.hom = 𝟙 _ := Over.w η[x.P.A]
      rw [Category.assoc, hw0, ← Category.assoc, a₁, Category.assoc, a₂]; simp
  have g := (isGen_iff w).1 hw
  have g'' := (isGen_iff w'').1 hw''
  obtain ⟨w', T⟩ := exists_cancel Y.t.PP.isLB w w'' g g'' x.P.isLB x'.P.isLB
  have r := (maps_iff w _ (fun _ => eSec Y.t.G) _ x.rig Y.t.PP.rig z _ (rigPull_le φ z he Y.t.PP.L)
    (fun _ => rfl)).1 hr
  have r'' := (maps_iff w'' _ (fun _ => eSec Y.t.G) _ x'.rig Y.t.PP.rig (spMap f ≫ z) _
    (rigPull_le (φ' ≫ φ) (spMap f ≫ z) he'' Y.t.PP.L) (fun _ => rfl)).1 hr''
  refine ⟨φ', he', w', hg''.trans hg.symm, dualMap f, hc.cancel hc'' hw0,
    (isGen_iff w').2 (T.pgen_cancel Y.t.PP.isLB g g''),
    (maps_iff w' _ (fun _ => eSec x.P.A) _ x'.rig x.rig (spMap f) _ (rigPull_le φ' (spMap f) he' x.P.L)
      (fun _ => rfl)).2 (T.pmaps_cancel Y.t.PP.isLB (fun _ => he') r r''),
    (KeyCancel.appLE_eq_iff_stalk w' x.th x'.th).2 fun Z q y i k hi hk => ?_, fun a => ?_, ?_, fun i => ?_⟩
  · obtain ⟨j, hj⟩ := exists_chart Y.t.PP.isLB (φ (φ' (q y)))
    have a := (appLE_eq_iff_stalk w (mem_of_comm hp.w hz) M.θ x.th).1 hs Z (q ≫ φ') y j i hj hi
    have b := (appLE_eq_iff_stalk w'' (mem_of_comm hc''.1.w (le_preimage_comp _ hz)) M.θ x'.th).1 hs'' Z q y j k hj hk
    rw [T Z q y j i k hj hi hk, ← Category.assoc, a, Units.val_mul, _root_.mul_assoc] at b
    exact (Units.mul_right_inj _).1 b
  · ext <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [dualMap]
  · apply hp.hom_ext
    · rw [Category.assoc, hv'', Category.assoc, hv, FlagMod.ev_spMap f z M.U hz, FlagMod.dualMap_comp, spMap_comp₀,
        Category.assoc]
      rfl
    · rw [Category.assoc, hw0, ← Category.assoc, Over.w, Category.assoc, Over.w]
      show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.KeyAtBC
