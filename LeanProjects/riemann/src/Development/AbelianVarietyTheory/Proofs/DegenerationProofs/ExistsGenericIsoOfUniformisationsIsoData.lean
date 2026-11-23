import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpandsGOfGenericRel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericIso

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaBaseChange GlobalTheory.ThetaDescent GlobalTheory.RigidSections

section Bundles

variable {Y Y' X X' N N' : Scheme.{0}} {L : LB X} {L' : LB X'} {M : LB N} {M' : LB N'}

theorem exists_pull_id {c : Y ⟶ X} {q : Y ⟶ N} {w : LB.Iso (L.pull c) (M.pull q)} (hw : w.IsGen) :
    ∃ u : LB.Iso (L.pull c) ((M.pull q).pull (𝟙 Y)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : M.ι) (i : L.ι), q (f z) ∈ M.U j → c (f z) ∈ L.U i →
        isoVal u f z (fun _ => j) i = isoVal w f z j i := by
  have le : ∀ p : (PUnit → (M.pull q).ι) × (L.pull c).ι, ((M.pull q).pull (𝟙 Y)).U p.1 ⊓ (L.pull c).U p.2 ≤
      (M.pull q).U (p.1 PUnit.unit) ⊓ (L.pull c).U p.2 := fun p x hx =>
    ⟨(mem_pull (F := 𝟙 Y)).1 hx.1, hx.2⟩
  let u : LB.Iso (L.pull c) ((M.pull q).pull (𝟙 Y)) := ⟨fun p => res (le p) (w.s (p.1 PUnit.unit, p.2))⟩
  have hu : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : (M.pull q).ι) (i : (L.pull c).ι), f z ∈ (M.pull q).U j →
      f z ∈ (L.pull c).U i → Geo.Tor.gw u f z j i = Geo.Tor.gw w f z (j PUnit.unit) i := fun Z f z j i hj hi =>
    gm_res f z (le (fun _ => j, i)) ⟨(mem_pull (F := 𝟙 Y)).2 hj, hi⟩ _
  refine ⟨u, (isGen_iff u).2 fun Z f z j j' i i' hj hj' hi hi' => ?_,
    fun Z f z j i hj hi => hu Z f z _ _ (mem_pull.2 hj) (mem_pull.2 hi)⟩
  rw [hu Z f z j i hj hi, hu Z f z j' i' hj' hi', Category.comp_id, gm_pull_g M q f z j j' hj hj']
  exact (isGen_iff w).1 hw Z f z _ _ i i' (mem_pull.1 hj) (mem_pull.1 hj') hi hi'

theorem exists_square (hL : L.IsLB) (hL' : L'.IsLB) (hM : M.IsLB) (hM' : M'.IsLB)
    {c₀ : Y ⟶ X} {q : Y ⟶ N} {w : LB.Iso (L.pull c₀) (M.pull q)} (hw : w.IsGen) {n : X ⟶ Y} (hn : n ≫ c₀ = 𝟙 X)
    {c₁ : Y' ⟶ X'} {q' : Y' ⟶ N'} {w' : LB.Iso (L'.pull c₁) (M'.pull q')} (hw' : w'.IsGen)
    {P : Y' ⟶ Y} {wM : LB.Iso (M'.pull q') (M.pull (P ≫ q))} (hwM : wM.IsGen) {Φ : Y' ⟶ X} (hΦ : Φ ≫ n = P) :
    ∃ v : LB.Iso (L'.pull c₁) (L.pull Φ), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (z : Z) (j : M.ι) (j' : M'.ι) (i : L.ι) (i' : L'.ι),
        q (P (f z)) ∈ M.U j → q' (f z) ∈ M'.U j' → Φ (f z) ∈ L.U i → c₁ (f z) ∈ L'.U i' →
        isoVal w (f ≫ P) z j i * isoVal v f z i i' = isoVal wM f z j j' * isoVal w' f z j' i' := by
  obtain ⟨u, hu, e⟩ := exists_pull_id hw'
  obtain ⟨v, hv, h⟩ := exists_side hL hL' hM (pull_isLB hM' q') hw n hn hu hwM Φ
    (by rw [← Category.assoc, hΦ, Category.id_comp])
  refine ⟨v, hv, fun Z f z j j' i i' a b c d => ?_⟩
  have := h Z f z j (fun _ => j') i i' a (mem_pull.2 b) c d
  rwa [hΦ, Category.comp_id, e Z f z j' i' b d] at this

end Bundles

section Sections

variable {S W : Scheme.{0}} {t : W ⟶ S} {A A' : Over S} [GrpObj A] [GrpObj A'] {Φ : A'.left ⟶ A.left}
  {L : LB A.left} {L' : LB A'.left}
  {ω : (Over.mk t ⊗ A).left ⟶ (Over.mk t ⊗ A').left} {Y Y' N N' V V' : Scheme.{0}} {M : LB N} {M' : LB N'}

theorem moved_sec_generic (hL : L.IsLB) (hL' : L'.IsLB)
    {c₀ : Y ⟶ A.left} {q : Y ⟶ N} {w : LB.Iso (L.pull c₀) (M.pull q)}
    {c₁ : Y' ⟶ A'.left} {n₁ : A'.left ⟶ Y'} (hn₁ : c₁ ≫ n₁ = 𝟙 _) {q' : Y' ⟶ N'} {w' : LB.Iso (L'.pull c₁) (M'.pull q')}
    {P : Y' ⟶ Y} {wM : LB.Iso (M'.pull q') (M.pull (P ≫ q))} (hP : P ≫ c₀ = c₁ ≫ Φ)
    {v₂ : LB.Iso (L'.pull c₁) (L.pull (c₁ ≫ Φ))}
    (hsq : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y') (z : Z) (j : M.ι) (j' : M'.ι) (i : L.ι) (i' : L'.ι),
        q (P (f z)) ∈ M.U j → q' (f z) ∈ M'.U j' → (c₁ ≫ Φ) (f z) ∈ L.U i → c₁ (f z) ∈ L'.U i' →
        isoVal w (f ≫ P) z j i * isoVal v₂ f z i i' = isoVal wM f z j j' * isoVal w' f z j' i')
    {v : LB.Iso L' (L.pull Φ)}
    (hv : ∀ (Z : Scheme.{0}) (f : Z ⟶ A'.left) (z : Z) (j : L.ι) (i : L'.ι),
      Φ (f z) ∈ L.U j → f z ∈ L'.U i → Geo.Tor.gw v f z j i = isoVal v₂ (f ≫ n₁) z j i)
    {m : V ⟶ Y} {h : V ⟶ (Over.mk t ⊗ A).left} {m' : V' ⟶ Y'} {h' : V' ⟶ (Over.mk t ⊗ A').left} {Ξ : V' ⟶ V}
    (x₁ : (Ξ ≫ h) ≫ ω = h') (x₂ : Ξ ≫ m = m' ≫ P) {k : ℕ}
    {s' : LB.Sec (LPow A' L' k (Over.mk t))} {s : LB.Sec (LPow A L k (Over.mk t))} (hs : Moved v ω s' s)
    {σ : LB.Sec (LB.LinComb M (K := Fin 1) (fun _ => m ≫ q) (fun _ => (k : ℤ)))}
    {σ' : LB.Sec (LB.LinComb M' (K := Fin 1) (fun _ => m' ≫ q') (fun _ => (k : ℤ)))}
    (H : GeneratorPullback.IsoRelM L M c₀ q w m k (snd (Over.mk t) A).left h s (m ≫ q) (𝟙 _) σ)
    (H' : GeneratorPullback.IsoRelM L' M' c₁ q' w' m' k (snd (Over.mk t) A').left h' s' (m' ≫ q') (𝟙 _) σ')
    (Z : Scheme.{0}) (r : Z ⟶ V') (z : Z) (j : M.ι) (j' : M'.ι)
    (hp : (r ≫ Ξ ≫ m ≫ q) z ∈ M.U j) (hp' : (r ≫ m' ≫ q') z ∈ M'.U j') :
    gs (r ≫ Ξ) z (LB.wchart M (fun _ : Fin 1 => m ≫ q) (fun _ => j)) (σ.f (fun _ => j)) =
      (isoVal wM (r ≫ m') z j j' ^ (k : ℤ)).val *
        gs r z (LB.wchart M' (fun _ : Fin 1 => m' ≫ q') (fun _ => j')) (σ'.f (fun _ => j')) := by
  obtain ⟨i, hi⟩ := exists_chart hL (Φ (c₁ (m' (r z))))
  obtain ⟨i', hi'⟩ := exists_chart hL' (c₁ (m' (r z)))
  have y₁ : (Ξ ≫ m) ≫ q = (m' ≫ P) ≫ q := by rw [x₂]
  have y₂ : (Ξ ≫ m) ≫ c₀ = m' ≫ c₁ ≫ Φ := by rw [x₂, Category.assoc, hP]
  have y₃ : (Ξ ≫ h) ≫ (snd (Over.mk t) A).left = m' ≫ c₁ ≫ Φ := by rw [Category.assoc, H.1, ← Category.assoc, y₂]
  have y₄ : ((Ξ ≫ h) ≫ ω) ≫ (snd (Over.mk t) A').left = m' ≫ c₁ := by rw [x₁, H'.1]
  have a := (isoRelM_iff w m k h H.1 _ H.2.1 s σ).1 H Z (r ≫ Ξ) z j i hp
    ((congrArg (fun f : V' ⟶ A.left => f (r z) ∈ L.U i) y₂).mpr hi)
  have a' := (isoRelM_iff w' m' k h' H'.1 _ H'.2.1 s' σ').1 H' Z r z j' i' hp' hi'
  have b := hs Z ((r ≫ Ξ) ≫ h) z i i'
    ((congrArg (fun f : V' ⟶ A.left => f (r z) ∈ L.U i) y₃).mpr hi)
    ((congrArg (fun f : V' ⟶ A'.left => f (r z) ∈ L'.U i') y₄).mpr hi')
  have e₁ : ((r ≫ Ξ) ≫ h) ≫ ω = r ≫ h' := by rw [← x₁]; simp only [Category.assoc]
  have e₂ : (r ≫ h') ≫ (snd (Over.mk t) A').left = (r ≫ m') ≫ c₁ := by
    rw [Category.assoc, H'.1, Category.assoc]
  rw [e₁, e₂, hv Z ((r ≫ m') ≫ c₁) z i i' hi hi', Category.assoc _ c₁, hn₁, Category.comp_id] at b
  have c := hsq Z (r ≫ m') z j j' i i' ((congrArg (fun f : V' ⟶ N => f (r z) ∈ M.U j) y₁).mp hp) hp' hi hi'
  have e₃ : (r ≫ Ξ) ≫ m = (r ≫ m') ≫ P := by rw [Category.assoc, x₂, Category.assoc r]
  rw [Category.comp_id] at a a'
  rw [e₃] at a
  refine a.trans ((congrArg _ b).trans (Eq.trans ?_ (congrArg _ a').symm))
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul, ← mul_zpow, ← mul_zpow, c]

end Sections

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {wG : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem GenericRel.exists_iso (hGl : GlobalFnsSt) (hR : AdmBase R I) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ wG)
    (ψ : A'.A ≅ A.A) (hψ : Φ.hom ≫ U.gen.hom = U'.gen.hom ≫ ψ.hom)
    {w : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R)))} (hw₀ : w.IsGen)
    {w' : LB.Iso (A'.L.pull U'.gen.hom.left) (U'.LG.L.pull (pullback.fst G'.hom (jK R)))} (hw' : w'.IsGen) :
    ∃ v : LB.Iso A'.L (A.L.pull ψ.hom.left), PGen v ∧
      ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k →
        (∀ a' : LB.Sec (LPow A'.A A'.L (k : ℤ) (TFK (R := R) F)), ∃ a : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)),
          Moved v (TFK (R := R) F ◁ ψ.inv).left a' a) ∧
        ∀ a' a b' b, Moved v (TFK (R := R) F ◁ ψ.inv).left a' a → FamRel hD F b'.s b.s →
          U.toUnifPre.ExpandsF F k w a b → U'.toUnifPre.ExpandsF F k w' a' b' := by
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]
  have hP : Φ.hom.left ≫ U.gen.hom.left = U'.gen.hom.left ≫ ψ.hom.left := congrArg (fun q => q.left) hψ
  have hΦ : (U'.gen.hom.left ≫ ψ.hom.left) ≫ U.gen.inv.left = Φ.hom.left := by
    rw [← Over.comp_left, ← Over.comp_left, ← hψ, Category.assoc, U.gen.hom_inv_id, Category.comp_id]
  obtain ⟨v₂, hv₂, hsq⟩ := exists_square A.isLB A'.isLB U.LG.isLB U'.LG.isLB hw₀ n₁ hw' hw.1 hΦ
  obtain ⟨v, hv, hvv⟩ := exists_unpull hv₂ _ n₂ (P := ψ.hom.left) (by rw [← Category.assoc, n₂, Category.id_comp])
  refine ⟨v, hv, fun F _ _ k hk => ⟨fun a' => exists_moved A.isLB A'.isLB ?_ n₂ hv₂ hvv a', ?_⟩⟩
  · exact congrArg (fun q => q.left) (show TFK (R := R) F ◁ ψ.inv ≫ snd _ _ ≫ ψ.hom = snd _ _ by simp)
  · rintro a' a b' b m hb ⟨σ, h₁, h₂⟩
    obtain ⟨-, σ', h₁', -⟩ := ((expandsF_bijective U'.toUnifPre F hGl hk (U'.expand k hk) hw').1 a').exists
    have x₁ : ((TFK (R := R) F ◁ Φ.hom).left ≫ (U.toUnifPre.genF F).left) ≫ (TFK (R := R) F ◁ ψ.inv).left =
        (U'.toUnifPre.genF F).left :=
      congrArg (fun q => q.left) (show (TFK (R := R) F ◁ Φ.hom ≫ U.toUnifPre.genF F) ≫ TFK (R := R) F ◁ ψ.inv =
          U'.toUnifPre.genF F by
        apply CartesianMonoidalCategory.hom_ext <;> simp [reassoc_of% hψ])
    have x₂ : (TFK (R := R) F ◁ Φ.hom).left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
        (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G')).left ≫ Φ.hom.left :=
      congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) Φ.hom)
    refine ⟨σ', h₁', expandsG_of_genericRel hGl R I hR D D' A A' G G' hG hG' U U' hD j hj Φ wG hw F k hk σ σ' b b'
      (fun Z r z jL jL' c c' => ?_) hb h₂⟩
    exact moved_sec_generic A.isLB A'.isLB n₃ hP hsq hvv x₁ x₂ m h₁ h₁' Z r z jL jL' c c'

theorem GenericRel.qkToAk_iff (hGl : GlobalFnsSt) (hR : AdmBase R I) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : LevelIso U.toUnifPre U'.toUnifPre hD j) (hw : GenericRel U.toUnifPre U'.toUnifPre hD j Φ wG)
    (ψ : A'.A ≅ A.A) [IsMonHom ψ.hom] (hψ : Φ.hom ≫ U.gen.hom = U'.gen.hom ≫ ψ.hom)
    (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (hk : 1 ≤ k) (p : QkPt D.toPre F k)
    (p' : QkPt D'.toPre F k) (x' : TFK (R := R) F ⟶ A'.A) (hy : p'.y = hD.xe.symm p.y)
    (hg : IsPullGtF (RingHom.id R) hD F p.g p'.g) :
    QkToAkU U'.toUnifPre F k p' x' ↔ QkToAkU U.toUnifPre F k p (x' ≫ ψ.hom) := by
  have gψ := isGrpPullback_of_iso ψ
  have ht : jFK (R := R) F ≫ 𝟙 _ = jFK (R := R) F := Category.comp_id _
  have hx : x'.left ≫ ψ.hom.left = (x' ≫ ψ.hom).left := rfl
  have hω₁ : (TFK (R := R) F ◁ ψ.inv).left ≫ (fst (TFK (R := R) F) A'.A).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) ψ.inv)
  have hω₂ : (TFK (R := R) F ◁ ψ.inv).left ≫ (snd (TFK (R := R) F) A'.A).left ≫ ψ.hom.left =
      (snd (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (show TFK (R := R) F ◁ ψ.inv ≫ snd _ _ ≫ ψ.hom = snd _ _ by simp)
  have hΩ₁ : (TFK (R := R) F ◁ ψ.hom).left ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R) F) A'.A).left :=
    congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) ψ.hom)
  have hΩ₂ : (TFK (R := R) F ◁ ψ.hom).left ≫ (snd (TFK (R := R) F) A.A).left =
      (snd (TFK (R := R) F) A'.A).left ≫ ψ.hom.left :=
    congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) ψ.hom)
  have hΩω : (TFK (R := R) F ◁ ψ.hom).left ≫ (TFK (R := R) F ◁ ψ.inv).left = 𝟙 _ :=
    congrArg (fun q => q.left) (show TFK (R := R) F ◁ ψ.hom ≫ TFK (R := R) F ◁ ψ.inv = 𝟙 _ by simp)
  have hF : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (RingHom.id R r)) := fun _ => rfl
  have hΘ₁ := prF_fst hD F
  have hΘ₂ := prF_snd hD F
  choose pl hpl using exists_pull hD F hGl k
  constructor
  · intro H w hw₀
    obtain ⟨w', hw'⟩ := U'.ext
    obtain ⟨hx1, H⟩ := H w' hw'
    obtain ⟨v, hv, hm⟩ := hw.exists_iso hGl hR hG hG' hj ψ hψ hw₀ hw'
    obtain ⟨mv, tr⟩ := hm F k hk
    refine ⟨pow_eq_one_of_pull ht gψ hx hx1, fun θ hθ => ?_⟩
    obtain ⟨θ', hθ', hact⟩ := exists_theta_pulled A.isLB A'.isLB ht gψ hv hω₁ hω₂ hΩ₁ hΩ₂ hΩω θ (x' := x')
      (by rw [hθ]; exact hx)
    obtain ⟨ν', hν', Hν'⟩ := H θ' hθ'
    have hl : ∀ i, DegPre.lineφ D'.toPre F p'.g.b i ≫
        (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) =
        𝟙 _ ≫ DegPre.lineφ D.toPre F p.g.b i := fun i => by
      obtain ⟨hψ, -⟩ := hg.2 0
      fin_cases i
      · exact hψ 3
      · exact hψ 2
    obtain ⟨ν, hν, pm⟩ := exists_pmaps_up ((isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB hl ν' hν'
    refine ⟨ν, hν, fun t t₂ s s₂ E E₂ hA => ?_⟩
    have bij := expandsF_bijective U.toUnifPre F hGl hk (U.expand k hk) hw₀
    have bij' := expandsF_bijective U'.toUnifPre F hGl hk (U'.expand k hk) hw'
    have hT := PhiPull.base_eq hF
    have inj : ∀ b b₂, pl b = pl b₂ → b = b₂ := fun b b₂ e => fam_ext fun α j => by
      obtain ⟨α', rfl⟩ := hD.xe.surjective α
      have h₂ := hpl b₂ α'
      rw [← e] at h₂
      exact sec_eq_of_pull D.toPre.P.isLB D'.toPre.P.isLB (IsIso.inv_hom_id (prF hD F))
        (FamFieldPull.famφ_pr hD F hT hΘ₁ hΘ₂ α') (hpl b α') h₂ j
    have key : ∀ a b, U.toUnifPre.ExpandsF F k w a b → ∃ a', Moved v (TFK (R := R) F ◁ ψ.inv).left a' a ∧
        U'.toUnifPre.ExpandsF F k w' a' (pl b) := fun a₀ b₀ E₀ => by
      obtain ⟨a', E⟩ := (bij'.2 (pl b₀)).exists
      obtain ⟨a, ha⟩ := mv a'
      obtain ⟨b, h⟩ := (bij.1 a).exists
      obtain rfl := inj _ _ ((bij'.1 a').unique (tr a' a _ b ha (hpl b) h) E)
      obtain rfl : a = a₀ := (bij.2 b).unique h E₀
      exact ⟨a', ha, E⟩
    obtain ⟨t', m, e⟩ := key t s E
    obtain ⟨t₂', m₂, e₂⟩ := key t₂ s₂ E₂
    have P' := (phiRel_iff hGl p' ν' hν' _ _).1 (Hν' t' t₂' _ _ e e₂ (hact t' t₂' t t₂ m m₂ hA))
    obtain ⟨s₃, P⟩ := exists_phi hGl p ν hν D.tau_bimult s
    have P'' := PhiPull.phiVal_pull hD hT hΘ₁ hΘ₂ hGl p p' hy hg ν ν' hl pm s s₃ _ _ (hpl s) (hpl s₃) P
    obtain rfl := inj _ _ (phi_unique p' ν' P'' P')
    exact (phiRel_iff hGl p ν hν _ _).2 P
  · intro H w' hw'
    obtain ⟨w, hw₀⟩ := U.ext
    obtain ⟨hx1, H⟩ := H w hw₀
    obtain ⟨v, hv, hm⟩ := hw.exists_iso hGl hR hG hG' hj ψ hψ hw₀ hw'
    obtain ⟨mv, tr⟩ := hm F k hk
    refine ⟨pow_eq_one_of_push ht gψ hx hx1, fun θ' hθ' => ?_⟩
    obtain ⟨θ, hθ, hact⟩ := exists_theta_moved A.isLB A'.isLB ht gψ hv hω₁ hω₂ θ' (x := x' ≫ ψ.hom)
      (by rw [hθ']; exact hx)
    obtain ⟨ν, hν, Hν⟩ := H θ hθ
    obtain ⟨ν', hν', Hν'⟩ := GlobalTheory.phiRel_transport hGl R R _ D.toPre D'.toPre hD F hF _ hΘ₁ hΘ₂ k p p' hy hg ν hν
    refine ⟨ν', hν', fun t' t₂' s' s₂' E E₂ hA => ?_⟩
    have bij := (expandsF_bijective U.toUnifPre F hGl hk (U.expand k hk) hw₀).1
    have bij' := (expandsF_bijective U'.toUnifPre F hGl hk (U'.expand k hk) hw').1
    have key : ∀ a' b', U'.toUnifPre.ExpandsF F k w' a' b' → ∃ a b, Moved v (TFK (R := R) F ◁ ψ.inv).left a' a ∧
        U.toUnifPre.ExpandsF F k w a b ∧ pl b = b' := fun a' b' E => by
      obtain ⟨a, ha⟩ := mv a'
      obtain ⟨b, h⟩ := (bij a).exists
      exact ⟨a, b, ha, h, (bij' a').unique (tr a' a _ b ha (hpl b) h) E⟩
    obtain ⟨t, s, m, e, rfl⟩ := key t' s' E
    obtain ⟨t₂, s₂, m₂, e₂, rfl⟩ := key t₂' s₂' E₂
    exact Hν' s s₂ _ _ (hpl s) (hpl s₂) (Hν t t₂ s s₂ e e₂ (hact t' t₂' t t₂ m m₂ hA))

end GlobalTheory.GenericIso

namespace GlobalTheory

open GlobalTheory.GenericIso in

theorem exists_generic_iso_of_unif : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D D' : DegData R I) (A A' : PolAV (Sp (FractionRing R))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ ψ : A'.A ≅ A.A, IsMonHom ψ.hom ∧ LBIso A'.L (A.L.pull ψ.hom.left) ∧ (∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (p' : QkPt D'.toPre F k) (x' : TFK (R := R) F ⟶ A'.A), p'.y = hD.xe.symm p.y → IsPullGtF (RingHom.id R) hD F p.g p'.g → (QkToAkU U'.toUnifPre F k p' x' ↔ QkToAkU U.toUnifPre F k p (x' ≫ ψ.hom))) ∧ ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.OAct O) (o' : D'.OAct O) (oA : A.OAct O) (oA' : A'.OAct O) (oG : RingAct G O) (oG' : RingAct G' O), U.OLinear O o oA oG → U'.OLinear O o' oA' oG' → (∀ (x : O) y, hD.xe (x • y) = x • hD.xe y) → (∀ x, o'.onB.act x ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (o.onB.act x)) → ∀ x, oA'.act x ≫ ψ.hom = ψ.hom ≫ oA.act x := by
  intro hL _ R _ _ I hR hI D D' A A' G G' _ _ _ _ hG hG' U U' hD
  obtain ⟨j, hj⟩ := exists_levelIso U.toUnifPre U'.toUnifPre hD hL.globalFns
  have hE := hj.enough hL.globalFns U.expand U'.expand
  obtain ⟨Φ, wG, hw⟩ := exists_genericRel hL R I hR D D' A A' G G' hG hG' U U' hD j hj hE
  obtain ⟨ψ, hψ⟩ : ∃ ψ : A'.A ≅ A.A, Φ.hom ≫ U.gen.hom = U'.gen.hom ≫ ψ.hom :=
    ⟨U'.gen.symm ≪≫ Φ ≪≫ U.gen, by simp⟩
  have := U.gen_hom
  have := U'.gen_hom
  have hm : IsMonHom ψ.hom := hL.rigidity _ _ _ A'.isAb A.isAb _ (by
    rw [← IsMonHom.one_hom U'.gen.hom, Category.assoc, ← hψ, ← Category.assoc, hw.one hL hR hI hG hG' hj hE,
      IsMonHom.one_hom])
  obtain ⟨w, hw₀⟩ := U.ext
  obtain ⟨w', hw'⟩ := U'.ext
  obtain ⟨v, hv, -⟩ := hw.exists_iso hL.globalFns hR hG hG' hj ψ hψ hw₀ hw'
  refine ⟨ψ, hm, ⟨v, (isGen_iff v).2 hv⟩, fun F _ _ k hk p p' x' hy hg =>
    hw.qkToAk_iff hL.globalFns hR hG hG' hj ψ hψ F k hk p p' x' hy hg, ?_⟩
  intro O _ _ _ _ o o' oA oA' oG oG' lin lin' hx hB x
  have h := hw.comm hL hR hI hG hG' hj hE (oG'.act x) (oG.act x) (hj.act_comm hL.globalFns lin lin' hx hB x)
  rw [← cancel_epi U'.gen.hom, ← reassoc_of% (lin'.ext x), ← hψ, ← reassoc_of% hψ, reassoc_of% h, lin.ext x]

end GlobalTheory
