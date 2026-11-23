import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallTorsionSetForEndomorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCardTorsionQuotSmulTopLePowFinrankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMapsTorsionIntoSmulTopStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

section Helpers

open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

namespace GlobalTheory.EqvFib

section Fib

variable {X' S : Scheme.{0}}

def fibEnd (G' : Over X') {σ : X' ⟶ X'} (mu : G'.left ⟶ G'.left) (hmu : mu ≫ G'.hom = G'.hom ≫ σ) (t : S ⟶ X')
    (ht : t ≫ σ = t) : (Over.pullback t).obj G' ⟶ (Over.pullback t).obj G' :=
  Over.homMk (pullback.lift (pullback.fst G'.hom t ≫ mu) (pullback.snd G'.hom t) (by
    rw [Category.assoc, hmu, ← Category.assoc, pullback.condition, Category.assoc, ht])) (pullback.lift_snd _ _ _)

theorem fibEnd_fst (G' : Over X') {σ : X' ⟶ X'} (mu : G'.left ⟶ G'.left) (hmu : mu ≫ G'.hom = G'.hom ≫ σ)
    (t : S ⟶ X') (ht : t ≫ σ = t) :
    (fibEnd G' mu hmu t ht).left ≫ pullback.fst G'.hom t = pullback.fst G'.hom t ≫ mu :=
  pullback.lift_fst _ _ _

theorem pullAct_fst (G' : Over X') [GrpObj G'] [IsCommMonObj G'] {O : Type} [CommRing O] (a : OAct O G')
    (t : S ⟶ X') (b : O) :
    ((OAct.pullback t G' a).act b).left ≫ pullback.fst G'.hom t = pullback.fst G'.hom t ≫ (a.act b).left :=
  pullback.lift_fst _ _ _

theorem pushHom_pull_left {T : Over S} {G' : Over X'} [GrpObj G'] (t : S ⟶ X') (z : T ⟶ (Over.pullback t).obj G') :
    (pushHom (isGrpPullback_pullback G' t) T z).left = z.left ≫ pullback.fst G'.hom t := rfl

theorem pull_ext {G' : Over X'} {t : S ⟶ X'} {T : Over S} (a b : T ⟶ (Over.pullback t).obj G')
    (h : a.left ≫ pullback.fst G'.hom t = b.left ≫ pullback.fst G'.hom t) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  exact (Over.w a).trans (Over.w b).symm

theorem isMonHom_fibEnd (G' : Over X') [GrpObj G'] {σ : X' ⟶ X'} (mu : G'.left ⟶ G'.left)
    (hG : IsGrpPullback G' G' σ mu) (t : S ⟶ X') (ht : t ≫ σ = t) :
    IsMonHom (fibEnd G' mu hG.1.w t ht) := by
  have h1 : IsGrpPullback ((Over.pullback t).obj G') G' t (pullback.fst G'.hom t ≫ mu) := by
    have := IsGrpPullback.comp (isGrpPullback_pullback G' t) hG
    rwa [ht] at this
  have h2 := isGrpPullback_pullback G' t
  refine isMonHom_of_mul _ fun T x y => pull_ext _ _ ?_
  have hx : (pushPt h1.1.w x).left = (x ≫ fibEnd G' mu hG.1.w t ht).left ≫ pullback.fst G'.hom t := by
    rw [Over.comp_left, Category.assoc, fibEnd_fst]; rfl
  have hy : (pushPt h1.1.w y).left = (y ≫ fibEnd G' mu hG.1.w t ht).left ≫ pullback.fst G'.hom t := by
    rw [Over.comp_left, Category.assoc, fibEnd_fst]; rfl
  have e2 := h2.2 T _ _ (pushPt h1.1.w x) (pushPt h1.1.w y) hx hy
  have e1 := h1.2 T x y (pushPt h1.1.w x) (pushPt h1.1.w y) rfl rfl
  rw [← e2, e1, Over.comp_left, Category.assoc, fibEnd_fst]

theorem fibEnd_act (G' : Over X') [GrpObj G'] [IsCommMonObj G'] {O : Type} [CommRing O] (a : OAct O G')
    {σ : X' ⟶ X'} (mu : G'.left ⟶ G'.left) (hmu : mu ≫ G'.hom = G'.hom ≫ σ)
    (hc : ∀ b, (a.act b).left ≫ mu = mu ≫ (a.act b).left) (t : S ⟶ X') (ht : t ≫ σ = t) (b : O) :
    (OAct.pullback t G' a).act b ≫ fibEnd G' mu hmu t ht = fibEnd G' mu hmu t ht ≫ (OAct.pullback t G' a).act b := by
  have A : ((OAct.pullback t G' a).act b).left ≫ pullback.fst G'.hom t = pullback.fst G'.hom t ≫ (a.act b).left :=
    pullback.lift_fst _ _ _
  apply pull_ext
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, fibEnd_fst, A, ← Category.assoc, A,
    Category.assoc, hc, ← Category.assoc, ← fibEnd_fst G' mu hmu t ht, Category.assoc]

end Fib

end GlobalTheory.EqvFib

namespace GlobalTheory.EqvFib

section Desc

theorem descend {X' G : Scheme.{0}} (h : G ⟶ X') (x : X') (K : Type) [Field K] [Algebra (X'.residueField x) K]
    (u : G ⟶ G)
    (H : ∀ (T : Scheme.{0}) (w : T ⟶ G) (v : T ⟶ Sp K),
      w ≫ h = v ≫ Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) K)) ≫ X'.fromSpecResidueField x →
        w ≫ u = w)
    (T : Scheme.{0}) (w : T ⟶ G) (v : T ⟶ Spec (X'.residueField x)) (hw : w ≫ h = v ≫ X'.fromSpecResidueField x) :
    w ≫ u = w := by
  have f₁ : Flat (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) K))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.Flat.of_isField (Field.toIsField _) _
  have f₂ : Surjective (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) K))) :=
    ⟨fun y => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum (X'.residueField x)) _ _⟩⟩
  have : Epi (pullback.fst v (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) K)))) := Flat.epi_of_flat_of_surjective _
  rw [← cancel_epi (pullback.fst v (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) K))))]
  have e := H _ (pullback.fst v (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) K))) ≫ w) (pullback.snd v (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) K))))
    (by rw [Category.assoc, hw, ← Category.assoc, pullback.condition, Category.assoc]; rfl)
  rwa [Category.assoc] at e

end Desc

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem m_one {X' : Scheme.{0}} {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X') (G' : Over X') [GrpObj G']
    (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) (hE : EqvAct.IsEqvAct ρ' G' act' m) : m 1 = 𝟙 _ := by
  have h := (hE.1 1).1
  have hw : m 1 ≫ G'.hom = G'.hom := by rw [h.w, map_one]; exact Category.comp_id _
  apply h.hom_ext
  · rw [Category.id_comp, ← hE.2.2 1 1, _root_.mul_one]
  · rw [hw, Category.id_comp]

theorem iter_fibEnd {X' S : Scheme.{0}} {Γ : Type} [Group Γ] (ρ' : Γ →* Aut X') (G' : Over X') [GrpObj G']
    (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) (hE : EqvAct.IsEqvAct ρ' G' act' m) (g0 : Γ)
    (t : S ⟶ X') (ht : t ≫ (ρ' g0).hom = t) (k : ℕ) :
    ((fun f => f ≫ fibEnd G' (m g0) (hE.1 g0).1.w t ht)^[k] (𝟙 _)).left ≫ pullback.fst G'.hom t =
      pullback.fst G'.hom t ≫ m (g0 ^ k) := by
  induction k with
  | zero => rw [Function.iterate_zero_apply, Over.id_left, Category.id_comp, pow_zero, m_one ρ' G' act' m hE,
      Category.comp_id]
  | succ k ih => rw [Function.iterate_succ_apply', Over.comp_left, Category.assoc, fibEnd_fst, ← Category.assoc, ih,
      Category.assoc, pow_succ', hE.2.2]

end Main

end GlobalTheory.EqvFib

namespace GlobalTheory.EqvFib

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem mb_ne_bot (l : Level H) : l.Mb ≠ ⊥ := by
  intro h
  have e := l.prod
  rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at e
  have h3 := l.three_le
  have : l.M = 0 := by exact_mod_cast e
  omega

theorem fib_gen (I : Ideal (𝓞 E)) (g : ℕ) (hNP : NeatPrime I g (Dw.p + Dw.q)) (hMb : l.Mb ≤ I)
    {Γ : Type} [Group Γ] [Finite Γ] (iota : Γ →* LevelAut Dw l) (hU : ∀ g0, UnipAt I (iota g0))
    {X' : Scheme.{0}} (ρ' : Γ →* Aut X') (G' : Over X') [GrpObj G'] (hS : IsSemiAbelian G')
    (act' : OAct (𝓞 E) G') (m : Γ → (G'.left ⟶ G'.left)) (hE : EqvAct.IsEqvAct ρ' G' act' m)
    (hT : EqvAct.TorsLevel I iota ρ' G' act' m) (g0 : Γ) (x : X') [CharZero (X'.residueField x)]
    (hx : X'.fromSpecResidueField x ≫ (ρ' g0).hom = X'.fromSpecResidueField x)
    (T : Scheme.{0}) (w : T ⟶ G'.left) (v : T ⟶ Spec (X'.residueField x))
    (hw : w ≫ G'.hom = v ≫ X'.fromSpecResidueField x) : w ≫ m g0 = w := by
  haveI := hS.comm
  haveI := Dw.fin
  haveI := Dw.proj
  have hcardI : Nat.card (𝓞 E ⧸ I) = g := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hNP.2.1]
  have hIfin : Finite (𝓞 E ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcardI]; exact hNP.1.ne_zero)
  have hIne : I ≠ ⊥ := by
    rintro rfl
    have e := hNP.2.1
    rw [Ideal.absNorm_bot] at e
    exact hNP.1.ne_zero e.symm
  have hImax : I.IsMaximal :=
    (Ideal.isPrime_of_irreducible_absNorm (by rw [hNP.2.1]; exact hNP.1)).isMaximal hIne
  let K := AlgebraicClosure (X'.residueField x)
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (X'.residueField x) K).injective
  let t : Sp K ⟶ X' := Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) K)) ≫ X'.fromSpecResidueField x
  have ht : t ≫ (ρ' g0).hom = t := by simp only [t, Category.assoc, hx]
  let α := fibEnd G' (m g0) (hE.1 g0).1.w t ht
  suffices hα : α = 𝟙 _ by
    refine descend G'.hom x K (m g0) (fun T w v hw => ?_) T w v hw
    have e := congrArg (fun f => pullback.lift w v hw ≫ f.left ≫ pullback.fst G'.hom t) hα
    have e' : pullback.lift w v hw ≫ pullback.fst G'.hom t = w := pullback.lift_fst _ _ _
    simp only [α, fibEnd_fst, Over.id_left, Category.id_comp] at e
    rw [← Category.assoc, e'] at e
    exact e.trans e'
  let actT := OAct.pullback t G' act'
  haveI hmon : IsMonHom α := isMonHom_fibEnd G' (m g0) (hE.1 g0) t ht
  have hact : ∀ a, actT.act a ≫ α = α ≫ actT.act a := fibEnd_act G' act' (m g0) _ (hE.2.1 g0) t ht
  have hiter : (fun f => f ≫ α)^[Nat.card Γ] (𝟙 _) = 𝟙 _ := by
    apply pull_ext
    rw [iter_fibEnd ρ' G' act' m hE g0 t ht, pow_card_eq_one', m_one ρ' G' act' m hE, Over.id_left,
      Category.id_comp, Category.comp_id]
  have hn : 0 < Nat.card Γ := Nat.card_pos

  let β := pushHom (isGrpPullback_pullback G' t) (𝟙_ (Over (Sp K)))
  have hβinj : Function.Injective β := fun a b hab => pull_ext a b (by
    rw [← pushHom_pull_left, ← pushHom_pull_left, hab])
  have hβact : ∀ z a, β (z ≫ actT.act a) = β z ≫ act'.act a := fun z a => Over.OverMorphism.ext (by
    rw [pushHom_pull_left, Over.comp_left, Over.comp_left, pushHom_pull_left, Category.assoc, pullAct_fst,
      Category.assoc])
  have hβα : ∀ z, (β (z ≫ α)).left = (β z).left ≫ m g0 := fun z => by
    rw [pushHom_pull_left, pushHom_pull_left, Over.comp_left, Category.assoc, fibEnd_fst, Category.assoc]
  let tor : (𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G') → Prop := fun z => ∀ a ∈ I, z ≫ actT.act a = 1
  have tor_one : tor 1 := fun a _ => by
    haveI := actT.hom a
    exact map_one (IsMonHom.monoidHom (actT.act a) _)
  have tor_mul : ∀ {z z'}, tor z → tor z' → tor (z * z') := fun {z z'} hz hz' a ha => by
    haveI := actT.hom a
    rw [MonObj.mul_comp, hz a ha, hz' a ha, _root_.mul_one]
  have tor_inv : ∀ {z}, tor z → tor z⁻¹ := fun {z} hz a ha => by
    haveI := actT.hom a
    have e := map_inv (IsMonHom.monoidHom (actT.act a) (𝟙_ (Over (Sp K)))) z
    refine e.trans ?_
    show (z ≫ actT.act a)⁻¹ = 1
    rw [hz a ha, inv_one]
  have tor_α : ∀ {z}, tor z → tor (z ≫ α) := fun {z} hz a ha => by
    rw [Category.assoc, ← hact, ← Category.assoc, hz a ha]
    exact map_one (IsMonHom.monoidHom α _)
  have torβ : ∀ {z}, tor z → EqvAct.IsTorsI I act' (β z) := fun {z} hz a ha => by
    rw [← hβact, hz a ha, map_one]
  obtain ⟨e, headd, helin, heinj, hemv⟩ := hT K ((𝟙_ (Over (Sp K))).hom ≫ t)
  have hfix : ((𝟙_ (Over (Sp K))).hom ≫ t) ≫ (ρ' g0).hom = (𝟙_ (Over (Sp K))).hom ≫ t := by
    rw [Category.assoc, ht]
  have hE1 : e (β 1) = 0 := by
    have e1 := headd (β 1) (β 1) (torβ tor_one) (torβ tor_one)
    rw [← map_mul, _root_.mul_one] at e1
    simpa using e1.symm
  have hEmul : ∀ {z z'}, tor z → tor z' → e (β (z * z')) = e (β z) + e (β z') := fun {z z'} hz hz' => by
    rw [map_mul]; exact headd _ _ (torβ hz) (torβ hz')
  have hEinv : ∀ {z}, tor z → e (β z⁻¹) = -e (β z) := fun {z} hz => by
    have e1 := hEmul hz (tor_inv hz)
    rw [_root_.mul_inv_cancel, hE1] at e1
    exact (neg_eq_of_add_eq_zero_right e1.symm).symm
  have hEα : ∀ {z}, tor z → e (β (z ≫ α)) = iota g0 (e (β z)) := fun {z} hz =>
    hemv g0 hfix (β z) (β (z ≫ α)) (torβ hz) (hβα z)
  have hEtors : ∀ {z}, tor z → ∀ a ∈ I, a • e (β z) = 0 := fun {z} hz a ha => by
    rw [← helin _ a (torβ hz), ← hβact, hz a ha, hE1]
  have hinj : ∀ {z z'}, tor z → tor z' → e (β z) = e (β z') → z = z' := fun {z z'} hz hz' h =>
    hβinj (heinj _ _ (torβ hz) (torβ hz') h)

  have hcount : ∃ T : Finset (𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G'), T.card ≤ g ^ (Dw.p + Dw.q) ∧
      ∀ z : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G', (∀ a ∈ I, z ≫ actT.act a = 1) → z ∈ T := by
    obtain ⟨hfin, hcard⟩ := GlobalTheory.T.finite_card_torsion_quot_smul_top_le_pow_finrank (𝓞 E) Dw.La I l.Mb hImax hIfin (mb_ne_bot l)
    let f : setOf tor → {y : GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelMod Dw l // ∀ a ∈ I, a • y = 0} := fun z => ⟨e (β z.1), hEtors z.2⟩
    have hf : Function.Injective f := fun z z' h => Subtype.ext (hinj z.2 z'.2 (congrArg Subtype.val h))
    haveI : Finite (setOf tor) := Finite.of_injective f hf
    have hP : (setOf tor).Finite := Set.toFinite _
    refine ⟨hP.toFinset, ?_, fun z hz => hP.mem_toFinset.2 hz⟩
    rw [← Nat.card_eq_card_finite_toFinset hP]
    calc Nat.card (setOf tor) ≤ Nat.card {y : GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms.LevelMod Dw l // ∀ a ∈ I, a • y = 0} :=
          Nat.card_le_card_of_injective f hf
      _ ≤ Nat.card (𝓞 E ⧸ I) ^ Module.finrank (𝓞 E) Dw.La := hcard
      _ = g ^ (Dw.p + Dw.q) := by rw [hcardI, Dw.rank]

  obtain ⟨m₀, hm₀⟩ := hU g0
  obtain ⟨j, hj⟩ := GlobalTheory.T.exists_pow_apply_mem_smul_univ_of_torsion (𝓞 E) Dw.La I l.Mb (liftLa (iota g0) - 1) m₀ hImax (mb_ne_bot l) hm₀
  have hunip : ∀ z : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G', (∀ a ∈ I, z ≫ actT.act a = 1) →
      (fun z : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G' => (z ≫ α) * z⁻¹)^[j] z = 1 := by
    intro z hz
    obtain ⟨Y, hY⟩ := Submodule.Quotient.mk_surjective _ (e (β z))
    have key : ∀ k, tor ((fun z : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G' => (z ≫ α) * z⁻¹)^[k] z) ∧
        e (β ((fun z : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback t).obj G' => (z ≫ α) * z⁻¹)^[k] z)) =
          Submodule.Quotient.mk (((liftLa (iota g0) - 1) ^ k) Y) := by
      intro k
      induction k with
      | zero => exact ⟨hz, by rw [Function.iterate_zero_apply, pow_zero, Module.End.one_apply, hY]⟩
      | succ k ih =>
        obtain ⟨h1, h2⟩ := ih
        rw [Function.iterate_succ_apply']
        refine ⟨tor_mul (tor_α h1) (tor_inv h1), ?_⟩
        rw [hEmul (tor_α h1) (tor_inv h1), hEα h1, hEinv h1, h2, pow_succ', Module.End.mul_apply,
          LinearMap.sub_apply, Module.End.one_apply, Submodule.Quotient.mk_sub, ← sub_eq_add_neg]
        congr 1
        exact (liftLa_spec (iota g0) _).symm
    have hYt : ∀ a ∈ I, a • Y ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) := fun a ha => by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, hY]
      exact hEtors hz a ha
    obtain ⟨h1, h2⟩ := key j
    apply hinj h1 tor_one
    rw [h2, hE1, Submodule.Quotient.mk_eq_zero]
    exact hj Y hYt
  exact GlobalTheory.T.exists_small_torsion_set_for_endomorphism E K ((Over.pullback t).obj G') actT α (Nat.card Γ) j g (Dw.p + Dw.q) I
    (IsSemiAbelian.pullback t G' hS) hmon hact hn hiter hNP.1 hNP.2.1 hNP.2.2.1 hNP.2.2.2 hcount hunip

end Gen

end GlobalTheory.EqvFib

end Helpers

theorem GlobalTheory.EqvFib.fibre_trivial_of_fixed : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), 1 ≤ Dw.p + Dw.q → l.A = 1 → ∀ (I : Ideal (𝓞 E)) (g : ℕ), NeatPrime I g (Dw.p + Dw.q) → l.Mb ≤ I → ∀ (Γ : Type) [Group Γ] [Finite Γ] (ι : Γ →* LevelAut Dw l), (∀ γ, UnipAt I (ι γ)) → ∀ (X' : Scheme.{0}) [IsIntegral X'] (φ : X' ⟶ X₀ TF.Y Z) (ρ' : Γ →* Aut X'), GlobalTheory.IsNormalScheme X' → IsProjOver (φ ≫ s₀ TF.Y Z) → ∀ m : Γ → ((GlobalTheory.EqvAct.pullG TF Z φ).left ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left), GlobalTheory.EqvAct.IsEqvAct ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → GlobalTheory.EqvAct.TorsLevel I ι ρ' (GlobalTheory.EqvAct.pullG TF Z φ) (GlobalTheory.EqvAct.pullAct TF Z φ) m → ∀ γ (x : X'), X'.fromSpecResidueField x ≫ (ρ' γ).hom = X'.fromSpecResidueField x → ∀ (T : Scheme.{0}) (w : T ⟶ (GlobalTheory.EqvAct.pullG TF Z φ).left) (v : T ⟶ Spec (X'.residueField x)), w ≫ (GlobalTheory.EqvAct.pullG TF Z φ).hom = v ≫ X'.fromSpecResidueField x → w ≫ m γ = w := by
  intro E _ _ _ H Dw l Xo c TF Z _ _ I g hNP hMb Γ _ _ iota hU X' _ φ ρ' _ _ m hE hT g0 x hx T w v hw
  haveI : CharZero (X'.residueField x) := by
    let q : Spec (X'.residueField x) ⟶ Sp c.F := X'.fromSpecResidueField x ≫ φ ≫ s₀ TF.Y Z
    exact charZero_of_injective_ringHom (Spec.preimage q).hom.injective
  exact GlobalTheory.EqvFib.fib_gen I g hNP hMb iota hU ρ' _ (IsSemiAbelian.pullback _ TF.Y.t.G TF.Y.t.semi) _ m hE hT g0 x
    hx T w v hw
