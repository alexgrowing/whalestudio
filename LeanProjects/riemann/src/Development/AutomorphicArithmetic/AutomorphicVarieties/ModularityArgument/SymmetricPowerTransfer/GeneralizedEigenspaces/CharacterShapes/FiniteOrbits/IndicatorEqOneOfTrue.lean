import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.UnitaryThreeTestFunctionHeckeRelations
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.UfDg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.TorPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.FinOrbSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutInvMulMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RestrictedProductBoxFibre
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OutOrbit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.OrbIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.RpExistsUnique
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Grp

private theorem indicator_eq_one_of_true {p : Prop} (h : p) : one p = 1 := if_pos h

private theorem one_f {p : Prop} (h : ¬ p) : one p = 0 := if_neg h

private theorem transfer {G : Type} [Group G] (S U2 : Subgroup G) (hS : S.Normal) (x : G) (U : Subgroup S)
    (hU : ∀ g : S, g ∈ U ↔ x⁻¹ * g * x ∈ U2) (a b : S) (hxa : Commute x (a : G)) (hxb : Commute x (b : G))
    (tor : ∀ u ∈ U2, ∃ c ∈ U2, u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S ∧ Commute c (a : G) ∧ Commute c (b : G))
    (fa : UpperTheory.V.AlgebraTools.FinOrb U2 U2 (a : G)) :
    UpperTheory.V.AlgebraTools.FinOrb U U a ∧ (∀ y : S, y ∈ DC U a ↔ x⁻¹ * y * x ∈ DC U2 (a : G)) ∧
      (UF U2 (a : G) b → UF U a b) := by
  let e : G →* G := (MulAut.conj x⁻¹).toMonoidHom
  have he : ∀ y, e y = x⁻¹ * y * x := fun y => by simp [e, MulAut.conj_apply]
  have hbij : Function.Bijective e := (MulAut.conj x⁻¹).bijective
  have hfix : ∀ y : G, Commute x y → e y = y := fun y h => by
    rw [he, mul_assoc, ← h.eq, inv_mul_cancel_left]
  obtain ⟨h1, h2, h3, -⟩ := dcMap G G ℂ e hbij U2 (a : G) (b : G)
  rw [hfix _ hxa] at h1 h2 h3
  rw [hfix _ hxb] at h3
  have hUe : U = (U2.comap e).subgroupOf S := by
    ext g
    rw [hU g, Subgroup.mem_subgroupOf, Subgroup.mem_comap, he]
  subst hUe
  have hc : ∀ u ∈ U2.comap e, ∃ c ∈ U2.comap e, c * (a : G) = a * c ∧ c * (b : G) = b * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S := by
    intro u hu
    obtain ⟨c, hc, c1, c2, c3, c4⟩ := tor (e u) hu
    refine ⟨x * c * x⁻¹, ?_, ((hxa.mul_left c3).mul_left hxa.inv_left).eq,
      ((hxb.mul_left c4).mul_left hxb.inv_left).eq, ?_, ?_⟩
    · rw [Subgroup.mem_comap, he]
      have : x⁻¹ * (x * c * x⁻¹) * x = c := by group
      rwa [this]
    · have := hS.conj_mem _ c1 x
      rw [he] at this
      have e1 : x * (x⁻¹ * u * x * c⁻¹) * x⁻¹ = u * (x * c * x⁻¹)⁻¹ := by group
      rwa [e1] at this
    · have := hS.conj_mem _ c2 x
      rw [he] at this
      have e1 : x * (c⁻¹ * (x⁻¹ * u * x)) * x⁻¹ = (x * c * x⁻¹)⁻¹ * u := by group
      rwa [e1] at this
  have hc' : ∀ u ∈ U2.comap e, ∃ c ∈ U2.comap e, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S := fun u hu => by
    obtain ⟨c, m, p, -, q⟩ := hc u hu
    exact ⟨c, m, p, q⟩
  obtain ⟨f, d, ufs, -⟩ := dcSub G ℂ S (U2.comap e) a (h2.2 fa) hc' hS
  refine ⟨f, fun y => ?_, fun h => ufs b hc (h3.2 h)⟩
  rw [d y, h1 (y : G), he]

private theorem form_inv {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] (B : Base Γ G V) (hω : B.ω = 1)
    (φ : B.Forms) (u : G) (hu : u ∈ B.U) (y : G) : φ.1 (y * u) = φ.1 y := by
  have h := φ.2.2 y ⟨u, hu⟩
  rw [hω] at h
  simpa using h

end Grp

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem val_unif_le : valuation k (unif k : k) ≤ 1 := by
  have hex : ∃ x : kˣ, valuation k (x : k) = uniformizer k := by
    obtain ⟨x, hx⟩ := valuation_surjective (uniformizer k)
    have h0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact uniformizer_ne_zero hx.symm
    exact ⟨Units.mk0 x h0, hx⟩
  have hu : valuation k (unif k : k) = uniformizer k := Classical.epsilon_spec hex
  rw [hu]
  exact uniformizer_lt_one.le

private theorem val_le_one {t : kˣ} (h : valuation k (t : k) < valuation k (unif k : k) ^ 2) :
    valuation k (t : k) ≤ 1 :=
  (h.trans_le (pow_le_one' val_unif_le 2)).le

private theorem dom_pair {t : kˣ} (h : valuation k (t : k) < valuation k (unif k : k) ^ 2) : Dom ![t, t⁻¹] := by
  have h1 := val_le_one h
  have h2 : 1 ≤ valuation k ((t⁻¹ : kˣ) : k) := by
    have e : valuation k (t : k) * valuation k ((t⁻¹ : kˣ) : k) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc (1 : _) = valuation k (t : k) * valuation k ((t⁻¹ : kˣ) : k) := e.symm
      _ ≤ 1 * valuation k ((t⁻¹ : kˣ) : k) := mul_le_mul_left h1 _
      _ = _ := one_mul _
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact le_rfl
  · exact h1.trans h2
  · exact absurd hij (by decide)
  · exact le_rfl

end Local

section Glob

variable {F : Type} [Field F] [NumberField F] {Δ : F}

private theorem sa_normal : (SA Δ).Normal := by
  refine ⟨fun n hn g => Subgroup.mem_iInf.2 fun v => ?_⟩
  have h1 : (rpg _ _).p v n ∈ SU (cv v Δ) := Subgroup.mem_iInf.1 hn v
  have := (MonoidHom.normal_ker _ : (SU (cv v Δ)).Normal).conj_mem _ h1 ((rpg _ _).p v g)
  show (rpg _ _).p v (g * n * g⁻¹) ∈ SU (cv v Δ)
  rwa [map_mul, map_mul, map_inv]

private theorem fs_loc (A : SD Δ) (hA : A.Ok) (t : Dat.Par F) (g y : DA Δ) (hg : A.IsElD g (SD.dS t)) (v : Pl F) (h : v ∈ A.Sg) :
    A.dat.fSv t v (y.1 v) = one (y.1 v ∈ DC (A.dat.J2v v) (g.1 v)) := by
  classical
  obtain ⟨-, -, hS, -, -⟩ := datOk F Δ A hA
  have h' : v ∈ A.dat.Sg := h
  have hSv : A.dat.S v = (A.V v).data (A.hs v h) (A.Ry v) (A.χ v) := dif_pos h
  have hJ : A.dat.J2v v = ((A.V v).J 2).comap (eD (A.hs v h)) := by
    refine (if_pos h').trans ?_
    rw [hSv]
    rfl
  have hf : A.dat.fSv t v (y.1 v) = (A.dat.S v).fS (t v) (y.1 v) := if_pos h'
  obtain ⟨hbij, -⟩ := eD_facts (Kv v) (Ov v) (hS v h).1 (hS v h).2.1 _ _ (A.hs v h) (hS v h).2.2.1
  have hd := (dcMap _ _ ℂ (eD (A.hs v h)) hbij ((A.V v).J 2) (g.1 v) (g.1 v)).1 (y.1 v)
  rw [hg.1 v h] at hd
  rw [hf, hSv, hJ]
  exact congrArg one (propext hd.symm)

private theorem fs_eq (A : SD Δ) (hA : A.Ok) (t : Dat.Par F) (g : DA Δ) (hg : A.IsElD g (SD.dS t)) (y : DA Δ) :
    A.dat.FS t y = one (y ∈ DC A.dat.U2 g) := by
  classical
  have hb : ∀ v ∉ A.Sg, A.dat.J2v v = KD _ (Ov v) := fun v hv => if_neg hv
  have hgU : ∀ v ∉ A.Sg, (rpg _ _).p v g ∈ A.dat.J2v v := fun v hv => by
    show g.1 v ∈ _
    rw [hg.2 v hv]
    exact one_mem _
  have hbox := (uFBox (Pl F) (DA Δ) (fun v => DX (cv v Δ)) (fun v => KD (cv v Δ) (Ov v)) A.dat.J2v (rpg _ _) A.Sg hb g hgU).1 y
  have hloc := fs_loc A hA t g y hg
  have hoff : ∀ v, v ∉ A.Sg → A.dat.fSv t v (y.1 v) = one (y.1 v ∈ KD _ (Ov v)) := fun v h => if_neg h
  by_cases hy : y ∈ DC A.dat.U2 g
  · rw [indicator_eq_one_of_true hy]
    have hm := hbox.1 hy
    refine (finprod_congr fun v => ?_).trans finprod_one
    by_cases h : v ∈ A.Sg
    · exact (hloc v h).trans (indicator_eq_one_of_true (hm.1 v h))
    · have h2 := hm.2 v h
      rw [hb v h] at h2
      exact (hoff v h).trans (indicator_eq_one_of_true h2)
  · rw [one_f hy]
    have hex : ∃ v, A.dat.fSv t v (y.1 v) = 0 := by
      by_contra hc
      push_neg at hc
      refine hy (hbox.2 ⟨fun v h => ?_, fun v h => ?_⟩)
      · by_contra c
        exact hc v ((hloc v h).trans (one_f c))
      · rw [hb v h]
        by_contra c
        exact hc v ((hoff v h).trans (one_f c))
    obtain ⟨v, hv⟩ := hex
    refine finprod_eq_zero _ v hv ?_
    refine (A.Sg.finite_toSet.union (Filter.eventually_cofinite.1
      (show ∀ᶠ v in Filter.cofinite, y.1 v ∈ KD (cv v Δ) (Ov v) from y.2))).subset fun w hw => ?_
    by_contra hc
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hw ((hoff w hc.1).trans (indicator_eq_one_of_true hc.2))

private theorem commute_of_off_of_isElD (A : SD Δ) (x : DA Δ) (hx : A.dat.Off x) (g : DA Δ) (d : ParN F 2) (hg : A.IsElD g d) : Commute x g := by
  refine Subtype.ext (funext fun v => ?_)
  show x.1 v * g.1 v = g.1 v * x.1 v
  by_cases h : v ∈ A.Sg
  · rw [hx v h, one_mul, mul_one]
  · rw [hg.2 v h, one_mul, mul_one]

private theorem key {V : Type} [AddCommGroup V] [Module ℂ V] (A : SD Δ) (hA : A.Ok) (ch : F → ℂ) (x : DA Δ)
    (B : Base (SU Δ) (SA Δ) V) (hx : A.dat.Off x) (hB : A.dat.IsBS ch x B) (g g' : SA Δ) (d d' : ParN F 2)
    (hg : A.IsElD g d) (hg' : A.IsElD g' d') (hd : A.DomS d) (hd' : A.DomS d') :
    UpperTheory.V.AlgebraTools.FinOrb B.U B.U g ∧ (∀ y : SA Δ, y ∈ DC B.U g ↔ x⁻¹ * y * x ∈ DC A.dat.U2 (g : DA Δ)) ∧ UF B.U g g' := by
  obtain ⟨f, hm⟩ := dMul F Δ A hA g d hg
  obtain ⟨a1, a2, a3⟩ := transfer (SA Δ) A.dat.U2 sa_normal x B.U hB.U g g' (commute_of_off_of_isElD A x hx _ _ hg) (commute_of_off_of_isElD A x hx _ _ hg') (fun u hu => by
    obtain ⟨c, hc, c1, c2, c3⟩ := torPart F Δ A hA u hu
    exact ⟨c, hc, c1, c2, c3 _ _ hg, c3 _ _ hg'⟩) f
  exact ⟨a1, a2, a3 (hm g' d' hg' hd hd')⟩

private theorem dom_cone (A : SD Δ) (t : Dat.Par F) (ht : A.Cone t) : A.DomS (SD.dS t) := fun v hv => dom_pair (ht v hv)

private theorem p1 {V : Type} [AddCommGroup V] [Module ℂ V] (A : SD Δ) (hA : A.Ok) (ch : F → ℂ) (x : DA Δ)
    (B : Base (SU Δ) (SA Δ) V) (hx : A.dat.Off x) (hB : A.dat.IsBS ch x B) (t : Dat.Par F) (g : SA Δ)
    (ht : A.Cone t) (hg : A.IsElD g (SD.dS t)) :
    UpperTheory.V.AlgebraTools.FinOrb B.U B.U g ∧ A.dat.FSx t x = fun y => one (y ∈ DC B.U g) := by
  obtain ⟨f, d, -⟩ := key A hA ch x B hx hB g g _ _ hg hg (dom_cone A t ht) (dom_cone A t ht)
  refine ⟨f, funext fun y => ?_⟩
  show A.dat.FS t (x⁻¹ * y * x) = _
  rw [fs_eq A hA t g hg]
  exact congrArg one (propext (d y).symm)

private theorem p2 {V : Type} [AddCommGroup V] [Module ℂ V] (A : SD Δ) (hA : A.Ok) (ch : F → ℂ) (x : DA Δ)
    (B : Base (SU Δ) (SA Δ) V) (hx : A.dat.Off x) (hB : A.dat.IsBS ch x B) (t : Dat.Par F) (g : SA Δ)
    (ht : A.Cone t) (hg : A.IsElD g (SD.dS t)) (φ : B.Forms) :
    ((Base.Tw.one B).R (A.dat.FSx t x) φ).1 = dcF B.U g φ.1 := by
  obtain ⟨f, e⟩ := p1 A hA ch x B hx hB t g ht hg
  rw [e]
  exact (opDc _ _ _ B hB.ω g f).2 φ

private theorem cone_mul (A : SD Δ) (t t' : Dat.Par F) (ht : A.Cone t) (ht' : A.Cone t') : A.Cone (t * t') := fun v hv => by
  have h1 := val_le_one (ht' v hv)
  show valuation (Kv v) ((t v * t' v : (Kv v)ˣ) : Kv v) < _
  rw [Units.val_mul, map_mul]
  exact (mul_le_of_le_one_right' h1).trans_lt (ht v hv)

private theorem dS_mul (t t' : Dat.Par F) : SD.dS (t * t') = SD.dS t * SD.dS t' := by
  funext v i
  fin_cases i <;> simp [SD.dS, mul_comm]

private theorem p3a {V : Type} [AddCommGroup V] [Module ℂ V] (A : SD Δ) (hA : A.Ok) (ch : F → ℂ) (x : DA Δ)
    (B : Base (SU Δ) (SA Δ) V) (hx : A.dat.Off x) (hB : A.dat.IsBS ch x B) (t t' : Dat.Par F)
    (ht : A.Cone t) (ht' : A.Cone t') (gs gs' : SA Δ) (hg : A.IsElD gs (SD.dS t)) (hg' : A.IsElD gs' (SD.dS t'))
    (hm' : A.IsElD ((gs * gs' : SA Δ) : DA Δ) (SD.dS (t * t'))) (φ : B.Forms) :
    ((Base.Tw.one B).R (A.dat.FSx (t * t') x) φ).1 =
      ((Base.Tw.one B).R (A.dat.FSx t x) ((Base.Tw.one B).R (A.dat.FSx t' x) φ)).1 := by
  have htt := cone_mul A t t' ht ht'
  have k1 := key A hA ch x B hx hB gs gs' _ _ hg hg' (dom_cone A t ht) (dom_cone A t' ht')
  have fb := (p1 A hA ch x B hx hB t' gs' ht' hg').1
  have fab := (p1 A hA ch x B hx hB (t * t') (gs * gs') htt hm').1
  rw [p2 A hA ch x B hx hB (t * t') (gs * gs') htt hm' φ, p2 A hA ch x B hx hB t gs ht hg,
    p2 A hA ch x B hx hB t' gs' ht' hg' φ]
  exact (uFMul _ V B.U gs gs' k1.1 fb fab k1.2.2 φ.1 fun u hu y => form_inv B hB.ω φ u hu y).symm

private theorem p3 {V : Type} [AddCommGroup V] [Module ℂ V] (A : SD Δ) (hA : A.Ok) (ch : F → ℂ) (x : DA Δ)
    (B : Base (SU Δ) (SA Δ) V) (hx : A.dat.Off x) (hB : A.dat.IsBS ch x B) (t t' : Dat.Par F)
    (ht : A.Cone t) (ht' : A.Cone t') :
    (Base.Tw.one B).R (A.dat.FSx (t * t') x) = (Base.Tw.one B).R (A.dat.FSx t x) * (Base.Tw.one B).R (A.dat.FSx t' x) := by
  have hE := elEx F Δ A hA
  have hElMul := hE.2.2.2.1
  have hElS := hE.2.2.2.2
  obtain ⟨g, hg⟩ := (hE.2.1 (SD.dS t)).exists
  obtain ⟨g', hg'⟩ := (hE.2.1 (SD.dS t')).exists
  have hm : A.IsElD (g * g') (SD.dS (t * t')) := by
    rw [dS_mul]
    exact hElMul g g' _ _ hg hg'
  refine LinearMap.ext fun φ => Subtype.ext ?_
  exact p3a A hA ch x B hx hB t t' ht ht' ⟨g, hElS g t hg⟩ ⟨g', hElS g' t' hg'⟩ hg hg' hm φ

end Glob

theorem UpperTheory.V.Z.Sym.So.sOps :
    UpperTheory.V.Z.Sym.So.SOps := by
  intro F _ _ Δ A hA V _ _ ch x B hx hB
  exact ⟨fun t g ht hg => p1 A hA ch x B hx hB t g ht hg, fun t g ht hg φ => p2 A hA ch x B hx hB t g ht hg φ,
    fun t t' ht ht' => p3 A hA ch x B hx hB t t' ht ht'⟩

end
