import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.USpreadU

open GlobalTheory.Poinc.GalTrans GlobalTheory.CechPic

theorem exists_model {O Ω R' R'' : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O]
    [IsIntegrallyClosed O] [Field Ω] [Algebra O Ω] [IsFractionRing O Ω] [CommRing R'] [CommRing R'']
    (f' : R' →+* O) (f'' : R'' →+* O) (P' : PolAV (Sp R')) (P'' : PolAV (Sp R'')) (Q : PolAV (Sp Ω))
    {b' : Q.A.left ⟶ P'.A.left} {b'' : Q.A.left ⟶ P''.A.left}
    (hb' : IsGrpPullback Q.A P'.A (spMap ((algebraMap O Ω).comp f')) b')
    (hb'' : IsGrpPullback Q.A P''.A (spMap ((algebraMap O Ω).comp f'')) b'')
    (l' : LBIso Q.L (P'.L.pull b')) (l'' : LBIso Q.L (P''.L.pull b'')) :
    ∃ (B : PolAV (Sp O)) (c' : B.A.left ⟶ P'.A.left) (c'' : B.A.left ⟶ P''.A.left) (j : Q.A.left ⟶ B.A.left),
      IsGrpPullback B.A P'.A (spMap f') c' ∧ IsGrpPullback B.A P''.A (spMap f'') c'' ∧
      LBIso B.L (P'.L.pull c') ∧ LBIso B.L (P''.L.pull c'') ∧
      IsGrpPullback Q.A B.A (spMap (algebraMap O Ω)) j ∧ j ≫ c' = b' ∧ j ≫ c'' = b'' ∧
      ∀ (t' : Sp R' ⟶ P'.A.left) (t'' : Sp R'' ⟶ P''.A.left) (w : Sp Ω ⟶ Q.A.left), t' ≫ P'.A.hom = 𝟙 _ →
        t'' ≫ P''.A.hom = 𝟙 _ → w ≫ Q.A.hom = 𝟙 _ → w ≫ b' = spMap ((algebraMap O Ω).comp f') ≫ t' →
        w ≫ b'' = spMap ((algebraMap O Ω).comp f'') ≫ t'' →
        ∃ w₀ : Sp O ⟶ B.A.left, w₀ ≫ B.A.hom = 𝟙 _ ∧ w₀ ≫ c' = spMap f' ≫ t' ∧ w₀ ≫ c'' = spMap f'' ≫ t'' := by
  obtain ⟨B, c', -, hc', lc'⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f') P'
  obtain ⟨B₂, c₂, -, hc₂, lc₂⟩ := GlobalTheory.PureType.exists_baseChange GlobalTheory.polBaseChange_holds (spMap f'') P''
  obtain ⟨j, hj, lj, ej⟩ := exists_factor P' B Q (sp_comp rfl) hc' hb' lc' l'
  obtain ⟨j₂, hj₂, lj₂, ej₂⟩ := exists_factor P'' B₂ Q (sp_comp rfl) hc₂ hb'' lc₂ l''
  obtain ⟨E, hE, lE, eE⟩ := exists_iso B B₂ Q hj hj₂ lj lj₂
  have hc'' : IsGrpPullback B.A P''.A (spMap f'') (E ≫ c₂) := (hE.comp hc₂).congr (Category.id_comp _) rfl
  have lc'' := lb_comp B.isLB B₂.isLB P''.isLB lE lc₂
  have ej'' : j ≫ E ≫ c₂ = b'' := by rw [← Category.assoc, eE, ej₂]
  generalize E ≫ c₂ = c'' at hc'' lc'' ej''
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap O Ω)) ∧ IsSchemeTheoreticallyDominant (spMap (algebraMap O Ω)) :=
    ExtUnique.spec_fractionRing O Ω
  have := P''.isAb.proper
  refine ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej, ej'', fun t' t'' w ht' ht'' hw e' e'' => ?_⟩
  have w₁ : (spMap f' ≫ t') ≫ P'.A.hom = 𝟙 _ ≫ spMap f' := by rw [Category.assoc, ht']; simp
  have k₁ := hc'.1.lift_fst _ _ w₁
  have k₂ := hc'.1.lift_snd _ _ w₁
  generalize hc'.1.lift _ _ w₁ = t at k₁ k₂
  have a₁ : spMap (algebraMap O Ω) ≫ t = w ≫ j := hc'.1.hom_ext
    (by rw [Category.assoc, k₁, Category.assoc, ej, e', ← Category.assoc, sp_comp rfl])
    (by rw [Category.assoc, k₂, Category.assoc, hj.1.w, reassoc_of% hw, Category.comp_id])
  have a₂ : t ≫ c'' = spMap f'' ≫ t'' := ExtUnique.hom_ext_of_dominant P''.A.hom
    (by rw [Category.assoc, hc''.1.w, reassoc_of% k₂, Category.assoc, ht'', Category.comp_id])
    (spMap (algebraMap O Ω))
    (by rw [reassoc_of% a₁, ej'', e'', ← Category.assoc, sp_comp rfl])
  exact ⟨t, k₂, k₁, a₂⟩

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (σ : X.Ω₁ →+* X.Ω₁) (s : X.M.Z ⟶ X.M.Z), X.M.pt ≫ s = spMap σ ≫ X.M.pt → ∀ (p : ℕ) [Fact p.Prime] (y : Sp (PadicAlgCl p) ⟶ X.M.Z) (S' S'' : ThetaSys X.o₁ X.Ω₁) (ρ' : S'.Real) (ρ'' : S''.Real), S'.R ≤ X.M.O (y (closedPoint (PadicAlgCl p))) → S''.R ≤ X.M.O ((y ≫ s) (closedPoint (PadicAlgCl p))) → ∀ (y₀ : S'.R →+* PadicAlgCl p) (y₁ : S''.R →+* PadicAlgCl p), (∀ a : S'.R, y₀ a = X.M.val y a) → (∀ a : S''.R, y₁ a = X.M.val (y ≫ s) a) → ∀ (u : ρ'.UTest p y₀) (u₁ : ρ''.UTest p y₁) (u' : Sp (ratHull S'.R) ⟶ Xo.XF cf) (u'' : Sp (ratHull S''.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S'.R))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left) (G'' : Over (Sp (ratHull S''.R))) (_ : GrpObj G'') (α'' : G''.left ⟶ ρ''.P.A.left) (β'' : G''.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat S'.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → IsGrpPullback G'' ρ''.P.A (spMap (toRat S''.R)) α'' → IsGrpPullback G'' Xo.univ.t.G (u'' ≫ pullback.fst _ _) β'' → LBIso (ρ''.P.L.pull α'') (Xo.univ.t.PP.L.pull β'') → ∀ (W₀ : Over (Sp X.Ω₁)) (_ : GrpObj W₀) (k₀ : W₀.left ⟶ G.left) (k₀'' : W₀.left ⟶ G''.left), IsGrpPullback W₀ G (spMap (ratHull S'.R).val.toRingHom) k₀ → IsGrpPullback W₀ G'' (spMap (σ.comp (ratHull S''.R).val.toRingHom)) k₀'' → k₀ ≫ β = k₀'' ≫ β'' → ∃ (P₀ : PolAV (Sp (PadicAlgCl p))) (a : P₀.A.left ⟶ u.A.A.left) (a' : P₀.A.left ⟶ u₁.A.A.left), IsGrpPullback P₀.A u.A.A (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p))) a ∧ IsGrpPullback P₀.A u₁.A.A (spMap (algebraMap (FractionRing u₁.V) (PadicAlgCl p))) a' ∧ LBIso P₀.L (u.A.L.pull a) ∧ LBIso P₀.L (u₁.A.L.pull a') ∧ (∀ (k' : S'.Gam) (k'' : S''.Gam) (w : Sp X.Ω₁ ⟶ W₀.left), w ≫ W₀.hom = 𝟙 _ → w ≫ k₀ ≫ α = spMap S'.R.val.toRingHom ≫ (ρ'.pt k').left → w ≫ k₀'' ≫ α'' = spMap (σ.comp S''.R.val.toRingHom) ≫ (ρ''.pt k'').left → ∃ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (x' : TFK (R := u₁.V) (PadicAlgCl p) ⟶ u₁.A.A), v ≫ P₀.A.hom = 𝟙 _ ∧ v ≫ a = x.left ∧ v ≫ a' = x'.left ∧ x.left ≫ u.φ = spMap y₀ ≫ (ρ'.pt k').left ∧ x'.left ≫ u₁.φ = spMap y₁ ≫ (ρ''.pt k'').left) ∧ ∀ (v : Sp (PadicAlgCl p) ⟶ P₀.A.left) (g : Sp (PadicAlgCl p) ⟶ G.left) (h : Sp (PadicAlgCl p) ⟶ G''.left), v ≫ P₀.A.hom = 𝟙 _ → g ≫ α = v ≫ a ≫ u.φ → h ≫ α'' = v ≫ a' ≫ u₁.φ → g ≫ β = h ≫ β'' := by
  intro E _ _ _ H Dw l Xo cf C X σ s hs p _ y S' S'' ρ' ρ'' h' h'' y₀ y₁ hy₀ hy₁ u u₁ u' u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ k₀'' hk₀ hk₀'' hkb
  haveI := X.ar.char
  set z := y (closedPoint (PadicAlgCl p)) with hz
  have hyz : Set.range y = {z} := RatModel.range_eq_singleton y _
  haveI : IsDedekindDomain X.o₁ := ArithBase.ded (Ω := X.Ω₁)
  haveI : IsNoetherianRing (X.M.O z) := X.M.isNoetherianRing_O z
  haveI : IsIntegrallyClosed (X.M.Z.presheaf.stalk z) := X.normal.isIntegrallyClosed_stalk z
  haveI : IsIntegrallyClosed (X.M.O z) := IsIntegrallyClosed.of_equiv (X.M.stalkEquiv z)

  have hU : ∀ n : ℤ, n ≠ 0 → IsUnit (n : X.M.O z) := fun n hn => by
    rw [← RatModel.val_ne_zero_iff hyz]
    have e := map_intCast (RatModel.valHom y z hyz) n
    rw [RatModel.valHom_apply] at e
    rw [e]
    exact Int.cast_ne_zero.2 hn
  have hmem : ∀ {x : X.Ω₁} (n : ℤ), n ≠ 0 → (n : X.Ω₁) * x ∈ X.M.O z → x ∈ X.M.O z := fun {x} n hn h => by
    obtain ⟨w, hw⟩ := hU n hn
    have e1 : (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * (n : X.Ω₁) = 1 := by
      have := congrArg (fun t : X.M.O z => (t : X.Ω₁)) w.inv_mul
      simpa [hw] using this
    have : x = (((w⁻¹ : (X.M.O z)ˣ) : X.M.O z) : X.Ω₁) * ((n : X.Ω₁) * x) := by rw [← mul_assoc, e1, one_mul]
    rw [this]; exact mul_mem (SetLike.coe_mem _) h
  have hR' : ratHull S'.R ≤ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    exact hmem n hn (h' h)
  have hR'' : ∀ x ∈ ratHull S''.R, σ x ∈ X.M.O z := fun x hx => by
    obtain ⟨n, hn, h⟩ := mem_ratHull.1 hx
    refine hmem n hn ?_
    have := map_mem_O hs (h'' h)
    rwa [map_mul, map_intCast] at this
  let f'Q : ratHull S'.R →+* X.M.O z := (Subalgebra.inclusion hR').toRingHom
  let f''Q : ratHull S''.R →+* X.M.O z := (σ.comp (ratHull S''.R).val.toRingHom).codRestrict (X.M.O z) fun x => hR'' x x.2
  let f' : S'.R →+* X.M.O z := f'Q.comp (toRat S'.R)
  let f'' : S''.R →+* X.M.O z := f''Q.comp (toRat S''.R)

  obtain ⟨Q, c, hc, lc⟩ := exists_pol_baseChange ρ'.P (spMap S'.R.val.toRingHom)
  have hW : IsGrpPullback W₀ ρ'.P.A (spMap S'.R.val.toRingHom) (k₀ ≫ α) :=
    (hk₀.comp hα).congr (spMap_val_toRat S'.R) rfl
  have ec : hW.1.lift c Q.A.hom hc.1.w ≫ k₀ ≫ α = c := hW.1.lift_fst _ _ _
  have ew : hW.1.lift c Q.A.hom hc.1.w ≫ W₀.hom = Q.A.hom := hW.1.lift_snd _ _ _
  generalize hW.1.lift c Q.A.hom hc.1.w = e at ec ew
  have he : IsGrpPullback Q.A W₀ (𝟙 _) e :=
    hW.cancel (hc.congr (Category.id_comp _).symm ec.symm) (by rw [ew, Category.comp_id])
  have hb'' : IsGrpPullback Q.A ρ''.P.A (spMap (σ.comp S''.R.val.toRingHom)) (e ≫ k₀'' ≫ α'') :=
    (he.comp (hk₀''.comp hα'')).congr (by rw [Category.id_comp]; exact sp_comp (RingHom.ext fun _ => rfl)) rfl
  have hA : pull α (cls ρ'.P.L ρ'.P.isLB) = pull β (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ'.P.isLB α (pull_isLB ρ'.P.isLB α)]
    exact (iso_iff (pull_isLB ρ'.P.isLB α) Xo.univ.t.PP.isLB β).1 hL
  have hA'' : pull α'' (cls ρ''.P.L ρ''.P.isLB) = pull β'' (cls _ Xo.univ.t.PP.isLB) := by
    rw [← cls_pull ρ''.P.isLB α'' (pull_isLB ρ''.P.isLB α'')]
    exact (iso_iff (pull_isLB ρ''.P.isLB α'') Xo.univ.t.PP.isLB β'').1 hL''
  have hk : pull k₀ (pull β (cls _ Xo.univ.t.PP.isLB)) = pull k₀'' (pull β'' (cls _ Xo.univ.t.PP.isLB)) := by
    rw [← pull_comp, ← pull_comp, hkb]
  have lb'' : LBIso Q.L (ρ''.P.L.pull (e ≫ k₀'' ≫ α'')) := by
    rw [iso_iff Q.isLB ρ''.P.isLB, (iso_iff Q.isLB ρ'.P.isLB _).1 lc, ← ec]
    simp only [pull_comp]
    rw [hA, hA'', hk]

  obtain ⟨B, c', c'', j, hc', hc'', lc', lc'', hj, ej', ej'', ht⟩ :=
    exists_model f' f'' ρ'.P ρ''.P Q (b' := c) (b'' := e ≫ k₀'' ≫ α'') hc hb'' lc lb''

  let v : X.M.O z →+* PadicAlgCl p := RatModel.valHom y z hyz
  have e₀ : v.comp f' = y₀ := RingHom.ext fun x => (hy₀ x).symm
  have e₁ : v.comp f'' = y₁ := RingHom.ext fun x => ((hy₁ x).trans (val_comp hs y _ (h'' x.2))).symm
  obtain ⟨P₀, d, hd, ld⟩ := exists_pol_baseChange B (spMap v)
  have hd' : IsGrpPullback P₀.A ρ'.P.A (spMap y₀) (d ≫ c') := (hd.comp hc').congr (sp_comp e₀) rfl
  have hd'' : IsGrpPullback P₀.A ρ''.P.A (spMap y₁) (d ≫ c'') := (hd.comp hc'').congr (sp_comp e₁) rfl
  obtain ⟨a, ha, la, ea, xa⟩ := exists_to_test u P₀ hd' (lb_comp P₀.isLB B.isLB ρ'.P.isLB ld lc')
  obtain ⟨a', ha', la', ea', xa'⟩ := exists_to_test u₁ P₀ hd'' (lb_comp P₀.isLB B.isLB ρ''.P.isLB ld lc'')
  refine ⟨P₀, a, a', ha, ha', la, la', fun k' k'' w hw c1 c2 => ?_, fun v₁ g h hv₁ hg hh => ?_⟩
  · have ww : w ≫ W₀.hom = 𝟙 _ ≫ 𝟙 _ := by rw [hw]; simp
    have q1 : he.1.lift w (𝟙 _) ww ≫ e = w := he.1.lift_fst _ _ _
    have q2 : he.1.lift w (𝟙 _) ww ≫ Q.A.hom = 𝟙 _ := he.1.lift_snd _ _ _
    generalize he.1.lift w (𝟙 _) ww = wQ at q1 q2
    obtain ⟨w₀, hw₀, g', g''⟩ := ht (ρ'.pt k').left (ρ''.pt k'').left wQ (Over.w (ρ'.pt k')) (Over.w (ρ''.pt k''))
      q2 (by rw [← ec, reassoc_of% q1, c1]; rfl) (by rw [reassoc_of% q1, c2]; rfl)
    have w₂ : (spMap v ≫ w₀) ≫ B.A.hom = 𝟙 _ ≫ spMap v := by rw [Category.assoc, hw₀]; simp
    have r1 : hd.1.lift _ _ w₂ ≫ d = spMap v ≫ w₀ := hd.1.lift_fst _ _ _
    have r2 : hd.1.lift _ _ w₂ ≫ P₀.A.hom = 𝟙 _ := hd.1.lift_snd _ _ _
    generalize hd.1.lift _ _ w₂ = wK at r1 r2
    obtain ⟨x, hx⟩ := xa wK r2
    obtain ⟨x', hx'⟩ := xa' wK r2
    refine ⟨wK, x, x', r2, hx, hx', ?_, ?_⟩
    · rw [← hx, Category.assoc, ea, reassoc_of% r1, g', ← Category.assoc, sp_comp e₀]
    · rw [← hx', Category.assoc, ea', reassoc_of% r1, g'', ← Category.assoc, sp_comp e₁]

  ·
    have wm' : c' ≫ ρ'.P.A.hom = (B.A.hom ≫ spMap f'Q) ≫ spMap (toRat S'.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc'.1.w
    have wm'' : c'' ≫ ρ''.P.A.hom = (B.A.hom ≫ spMap f''Q) ≫ spMap (toRat S''.R) := by
      rw [Category.assoc, sp_comp rfl]; exact hc''.1.w
    have m1 : hα.1.lift c' _ wm' ≫ α = c' := hα.1.lift_fst _ _ _
    have m2 : hα.1.lift c' _ wm' ≫ G.hom = B.A.hom ≫ spMap f'Q := hα.1.lift_snd _ _ _
    have m1'' : hα''.1.lift c'' _ wm'' ≫ α'' = c'' := hα''.1.lift_fst _ _ _
    have m2'' : hα''.1.lift c'' _ wm'' ≫ G''.hom = B.A.hom ≫ spMap f''Q := hα''.1.lift_snd _ _ _
    generalize hα.1.lift c' _ wm' = m' at m1 m2
    generalize hα''.1.lift c'' _ wm'' = m'' at m1'' m2''
    have key : m' ≫ β = m'' ≫ β'' := by
      haveI := Xo.univ.proper
      haveI : IsSeparated Xo.s := GlobalTheory.LevelQuotRep.isSeparated_of_qproj Xo.qproj
      obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap (X.M.O z) X.Ω₁)) ∧
          IsSchemeTheoreticallyDominant (spMap (algebraMap (X.M.O z) X.Ω₁)) :=
        ExtUnique.spec_fractionRing (X.M.O z) X.Ω₁
      haveI := B.isAb.smooth
      haveI : IsSchemeTheoreticallyDominant j := .of_isPullback hj.1.flip
      refine ExtUnique.hom_ext_of_dominant (Xo.univ.t.G.hom ≫ Xo.s ≫ terminal.from _) (terminal.hom_ext _ _) j ?_
      have n1a : (j ≫ m') ≫ α = (e ≫ k₀) ≫ α := by rw [Category.assoc, m1, ej', Category.assoc, ec]
      have n1b : (j ≫ m') ≫ G.hom = (e ≫ k₀) ≫ G.hom := by
        rw [Category.assoc, m2, reassoc_of% hj.1.w, Category.assoc, hk₀.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n1 : j ≫ m' = e ≫ k₀ := hα.1.hom_ext n1a n1b
      have n2a : (j ≫ m'') ≫ α'' = (e ≫ k₀'') ≫ α'' := by rw [Category.assoc, m1'', ej'', Category.assoc]
      have n2b : (j ≫ m'') ≫ G''.hom = (e ≫ k₀'') ≫ G''.hom := by
        rw [Category.assoc, m2'', reassoc_of% hj.1.w, Category.assoc, hk₀''.1.w, reassoc_of% ew]
        exact congrArg (Q.A.hom ≫ ·) (sp_comp (RingHom.ext fun _ => rfl))
      have n2 : j ≫ m'' = e ≫ k₀'' := hα''.1.hom_ext n2a n2b
      rw [reassoc_of% n1, reassoc_of% n2, hkb]
    have hg' : g ≫ α = v₁ ≫ d ≫ c' := by rw [hg, ea]
    have hh' : h ≫ α'' = v₁ ≫ d ≫ c'' := by rw [hh, ea']
    have g1 : g = v₁ ≫ d ≫ m' := hα.1.hom_ext (by rw [hg', Category.assoc, Category.assoc, m1])
      ((existsUnique_ratPoint S'.R (g ≫ α ≫ ρ'.P.A.hom)).unique (by rw [Category.assoc, hα.1.w])
        (by simp only [Category.assoc]; rw [← hα.1.w, reassoc_of% m1, ← reassoc_of% hg']))
    have h1 : h = v₁ ≫ d ≫ m'' := hα''.1.hom_ext (by rw [hh', Category.assoc, Category.assoc, m1''])
      ((existsUnique_ratPoint S''.R (h ≫ α'' ≫ ρ''.P.A.hom)).unique (by rw [Category.assoc, hα''.1.w])
        (by simp only [Category.assoc]; rw [← hα''.1.w, reassoc_of% m1'', ← reassoc_of% hh']))
    rw [g1, h1]; simp only [Category.assoc, key]

end GlobalTheory.UPoinc.USpreadU
