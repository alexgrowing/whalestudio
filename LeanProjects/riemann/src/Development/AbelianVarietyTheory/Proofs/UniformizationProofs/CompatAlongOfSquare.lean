import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace UnifPullRig

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Core

variable {S S' B B' T T' T₁ T₁' G G' A A' : Scheme.{0}}

def RigAlong {L : LB G} {M : LB A} {f : T ⟶ G} {p : T ⟶ A} (w : LB.Iso (L.pull f) (M.pull p))
    (ε : S ⟶ T) (i : S ⟶ B) {eG : B ⟶ G} {eA : B ⟶ A} (rL : LB.Gen (L.pull eG))
    (rM : LB.Gen (M.pull eA)) : Prop :=
  ∀ (q : (PUnit → M.ι) × (PUnit → L.ι)) (V : S.Opens)
    (h₁ : V ≤ ε ⁻¹ᵁ ((M.pull p).U q.1 ⊓ (L.pull f).U q.2))
    (h₂ : V ≤ i ⁻¹ᵁ (L.pull eG).U q.2) (h₃ : V ≤ i ⁻¹ᵁ (M.pull eA).U q.1),
    res h₁ (pullU ε _ (w.s q)) * res h₂ (pullU i _ (rL.s q.2)) = res h₃ (pullU i _ (rM.s q.1))

def CompatAlong {L : LB G} {M : LB A} {f : T ⟶ G} {p : T ⟶ A} {f₁ : T₁ ⟶ G} {p₁ : T₁ ⟶ A}
    (w₁ : LB.Iso (L.pull f₁) (M.pull p₁)) (w : LB.Iso (L.pull f) (M.pull p)) (m : T ⟶ T₁) : Prop :=
  ∀ (q : (PUnit → M.ι) × (PUnit → L.ι)) (V : T.Opens)
    (h₁ : V ≤ m ⁻¹ᵁ ((M.pull p₁).U q.1 ⊓ (L.pull f₁).U q.2))
    (h₂ : V ≤ (M.pull p).U q.1 ⊓ (L.pull f).U q.2),
    res h₁ (pullU m _ (w₁.s q)) = res h₂ (w.s q)

def Square {L : LB G} {M : LB A} {L' : LB G'} {M' : LB A'} {F : G' ⟶ G} {E : A' ⟶ A}
    {f : T ⟶ G} {p : T ⟶ A} {f' : T' ⟶ G'} {p' : T' ⟶ A'}
    (wL : LB.Iso L' (L.pull F)) (wM : LB.Iso M' (M.pull E))
    (w : LB.Iso (L.pull f) (M.pull p)) (w' : LB.Iso (L'.pull f') (M'.pull p')) (h : T' ⟶ T) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ T') (z : Z) (jM : M.ι) (jM' : M'.ι) (jL : L.ι) (jL' : L'.ι),
    E (p' (r z)) ∈ M.U jM → p' (r z) ∈ M'.U jM' → F (f' (r z)) ∈ L.U jL → f' (r z) ∈ L'.U jL' →
    gw wM (r ≫ p') z jM jM' * gw w' r z jM' (fun _ => jL') =
      gw w (r ≫ h) z jM (fun _ => jL) * gw wL (r ≫ f') z jL jL'

theorem gm_res_pull {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) {U : X.Opens} {V : Y.Opens}
    (hle : V ≤ g ⁻¹ᵁ U) (hz : r z ∈ V) (a : Γ(X, U)ˣ) :
    gm r z V (res hle (pullU g U a)) = gm (r ≫ g) z U a :=
  (gm_res r z hle hz _).trans (gm_pull r g z U (hle hz) a)

theorem pt_of_eq {X Y Y' Z : Scheme.{0}} {a : X ⟶ Y} {b : Y ⟶ Z} {c : X ⟶ Y'} {d : Y' ⟶ Z}
    (h : a ≫ b = c ≫ d) (x : X) : b (a x) = d (c x) :=
  congrArg (fun g => g x) h

variable {L : LB G} {M : LB A} {L' : LB G'} {M' : LB A'} {F : G' ⟶ G} {E : A' ⟶ A}
    {f : T ⟶ G} {p : T ⟶ A} {f' : T' ⟶ G'} {p' : T' ⟶ A'}
    {f₁ : T₁ ⟶ G} {p₁ : T₁ ⟶ A} {f₁' : T₁' ⟶ G'} {p₁' : T₁' ⟶ A'}

theorem RigAlong.stalk {w : LB.Iso (L.pull f) (M.pull p)} {ε : S ⟶ T} {i : S ⟶ B} {eG : B ⟶ G}
    {eA : B ⟶ A} {rL : LB.Gen (L.pull eG)} {rM : LB.Gen (M.pull eA)} (H : RigAlong w ε i rL rM)
    (hf : ε ≫ f = i ≫ eG) (hp : ε ≫ p = i ≫ eA) {Z : Scheme.{0}} (r : Z ⟶ S) (z : Z) (jM : M.ι)
    (jL : L.ι) (hM : p (ε (r z)) ∈ M.U jM) (hL : f (ε (r z)) ∈ L.U jL) :
    gw w (r ≫ ε) z jM (fun _ => jL) * gm (r ≫ i) z ((L.pull eG).U (fun _ => jL)) (rL.s (fun _ => jL)) =
      gm (r ≫ i) z ((M.pull eA).U (fun _ => jM)) (rM.s (fun _ => jM)) := by
  have hz : r z ∈ ε ⁻¹ᵁ ((M.pull p).U (fun _ => jM) ⊓ (L.pull f).U (fun _ => jL)) ⊓
      (i ⁻¹ᵁ (L.pull eG).U (fun _ => jL) ⊓ i ⁻¹ᵁ (M.pull eA).U (fun _ => jM)) :=
    ⟨⟨mem_pull.2 hM, mem_pull.2 hL⟩, mem_pull.2 (pt_of_eq hf (r z) ▸ hL),
      mem_pull.2 (pt_of_eq hp (r z) ▸ hM)⟩
  have e := congrArg (gm r z _) (H (fun _ => jM, fun _ => jL) _ inf_le_left
    (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right))
  exact (congrArg₂ (· * ·) (gm_res_pull r ε z _ hz _) (gm_res_pull r i z _ hz _)).symm.trans
    ((map_mul _ _ _).symm.trans (e.trans (gm_res_pull r i z _ hz _)))

theorem CompatAlong.stalk {w₁ : LB.Iso (L.pull f₁) (M.pull p₁)} {w : LB.Iso (L.pull f) (M.pull p)}
    {m : T ⟶ T₁} (H : CompatAlong w₁ w m) (hf : m ≫ f₁ = f) (hp : m ≫ p₁ = p) {Z : Scheme.{0}}
    (r : Z ⟶ T) (z : Z) (jM : M.ι) (jL : L.ι) (hM : p (r z) ∈ M.U jM) (hL : f (r z) ∈ L.U jL) :
    gw w₁ (r ≫ m) z jM (fun _ => jL) = gw w r z jM (fun _ => jL) := by
  subst hf hp
  have hz : r z ∈ m ⁻¹ᵁ ((M.pull p₁).U (fun _ => jM) ⊓ (L.pull f₁).U (fun _ => jL)) ⊓
      ((M.pull (m ≫ p₁)).U (fun _ => jM) ⊓ (L.pull (m ≫ f₁)).U (fun _ => jL)) :=
    ⟨⟨mem_pull.2 hM, mem_pull.2 hL⟩, mem_pull.2 hM, mem_pull.2 hL⟩
  have e := congrArg (gm r z _) (H (fun _ => jM, fun _ => jL) _ inf_le_left inf_le_right)
  exact (gm_res_pull r m z _ hz _).symm.trans (e.trans (gm_res r z _ hz _))

theorem compatAlong_of_square (hL : L.IsLB) (hM : M.IsLB)
    {wL : LB.Iso L' (L.pull F)} {wM : LB.Iso M' (M.pull E)}
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')} {h : T' ⟶ T}
    {w₁ : LB.Iso (L.pull f₁) (M.pull p₁)} {w₁' : LB.Iso (L'.pull f₁') (M'.pull p₁')} {h₁ : T₁' ⟶ T₁}
    {m : T ⟶ T₁} {m' : T' ⟶ T₁'} (Q : Square wL wM w w' h) (Q₁ : Square wL wM w₁ w₁' h₁)
    (H : CompatAlong w₁ w m) (hf : m ≫ f₁ = f) (hp : m ≫ p₁ = p) (hf' : m' ≫ f₁' = f')
    (hp' : m' ≫ p₁' = p') (hF : h ≫ f = f' ≫ F) (hE : p' ≫ E = h ≫ p) (hm : m' ≫ h₁ = h ≫ m) :
    CompatAlong w₁' w' m' := by
  rintro ⟨qM, qL⟩ V a₁ a₂
  refine unit_ext fun y hy => ?_
  obtain ⟨jM, hjM⟩ := exists_chart hM (E (p' y))
  obtain ⟨jL, hjL⟩ := exists_chart hL (F (f' y))
  have bM : p' y ∈ M'.U (qM ⟨⟩) := mem_pull.1 (a₂ hy).1
  have bL : f' y ∈ L'.U (qL ⟨⟩) := mem_pull.1 (a₂ hy).2
  have e₀ := Q _ (𝟙 T') y jM (qM ⟨⟩) jL (qL ⟨⟩) hjM bM hjL bL
  have e₂ := H.stalk hf hp (𝟙 T' ≫ h) y jM jL (pt_of_eq hE y ▸ hjM) ((pt_of_eq hF y).symm ▸ hjL)
  subst hf' hp'
  have e₁ := Q₁ _ (𝟙 T' ≫ m') y jM (qM ⟨⟩) jL (qL ⟨⟩) hjM bM hjL bL
  rw [Category.assoc, Category.assoc, Category.assoc, hm, ← Category.assoc _ h m, e₂, ← e₀] at e₁
  exact (gm_res_pull _ m' y a₁ hy _).trans ((mul_left_cancel e₁).trans (gm_res _ y a₂ hy _).symm)

theorem rigAlong_of_square (hL : L.IsLB) (hM : M.IsLB)
    {wL : LB.Iso L' (L.pull F)} {wM : LB.Iso M' (M.pull E)}
    {w : LB.Iso (L.pull f) (M.pull p)} {w' : LB.Iso (L'.pull f') (M'.pull p')} {h : T' ⟶ T}
    {ε : S ⟶ T} {i : S ⟶ B} {eG : B ⟶ G} {eA : B ⟶ A} {rL : LB.Gen (L.pull eG)}
    {rM : LB.Gen (M.pull eA)}
    {ε' : S' ⟶ T'} {i' : S' ⟶ B'} {eG' : B' ⟶ G'} {eA' : B' ⟶ A'} {rL' : LB.Gen (L'.pull eG')}
    {rM' : LB.Gen (M'.pull eA')} {b : B' ⟶ B} {σ : S' ⟶ S}
    (Q : Square wL wM w w' h) (H : RigAlong w ε i rL rM)
    (PL : PMaps wL (K := PUnit) (fun _ => eG') (fun _ => eG) (fun _ => 1) rL' rL b)
    (PM : PMaps wM (K := PUnit) (fun _ => eA') (fun _ => eA) (fun _ => 1) rM' rM b)
    (hf : ε ≫ f = i ≫ eG) (hp : ε ≫ p = i ≫ eA) (hf' : ε' ≫ f' = i' ≫ eG') (hp' : ε' ≫ p' = i' ≫ eA')
    (hF : h ≫ f = f' ≫ F) (hE : p' ≫ E = h ≫ p) (hε : ε' ≫ h = σ ≫ ε) (hσ : σ ≫ i = i' ≫ b) :
    RigAlong w' ε' i' rL' rM' := by
  rintro ⟨qM, qL⟩ V a₁ a₂ a₃
  refine unit_ext fun y hy => ?_
  obtain ⟨jM, hjM⟩ := exists_chart hM (E (p' (ε' y)))
  obtain ⟨jL, hjL⟩ := exists_chart hL (F (f' (ε' y)))
  have bM : p' (ε' y) ∈ M'.U (qM ⟨⟩) := mem_pull.1 (a₁ hy).1
  have bL : f' (ε' y) ∈ L'.U (qL ⟨⟩) := mem_pull.1 (a₁ hy).2
  have e₀ := Q _ ε' y jM (qM ⟨⟩) jL (qL ⟨⟩) hjM bM hjL bL
  have e₁ := H.stalk hf hp σ y jM jL (by rw [← pt_of_eq hε y, ← pt_of_eq hE]; exact hjM)
    (by rw [← pt_of_eq hε y, pt_of_eq hF]; exact hjL)
  have e₂ := PL _ i' y (fun _ => jL) qL (fun _ => pt_of_eq hf' y ▸ hjL) (fun _ => pt_of_eq hf' y ▸ bL)
  have e₃ := PM _ i' y (fun _ => jM) qM (fun _ => pt_of_eq hp' y ▸ hjM) (fun _ => pt_of_eq hp' y ▸ bM)
  rw [Fintype.prod_unique, zpow_one] at e₂ e₃
  rw [hσ, ← hε] at e₁
  rw [hf', hp'] at e₀
  have e₄ := (congrArg (gw w (ε' ≫ h) y jM (fun _ => jL) * ·) e₂).symm.trans (e₁.trans e₃)
  rw [← _root_.mul_assoc] at e₄
  have e₅ := (congrArg (· * gm i' y (LB.wchart L' (fun _ => eG') qL) (rL'.s qL)) e₀).trans e₄
  have e₆ := mul_left_cancel ((_root_.mul_assoc _ _ _).symm.trans e₅)
  refine (map_mul _ _ _).trans ((congrArg₂ (· * ·) (gm_res_pull _ ε' y a₁ hy _)
    (gm_res_pull _ i' y a₂ hy _)).trans (Eq.trans ?_ (gm_res_pull _ i' y a₃ hy _).symm))
  rw [Category.id_comp, Category.id_comp]
  exact e₆

end Core

section Geometry

variable {R : Type} [CommRing R] [IsDomain R] (I : Ideal R)

omit [IsDomain R] in
theorem eSec_hom (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] :
    eSec G ≫ G.hom = 𝟙 _ := Over.w η[G]

omit [IsDomain R] in
theorem thickMap_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [IsDomain R] in
theorem eSec_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] :
    eSec (thickObj R I e G) ≫ (fstG I e G).left = thick R I e ≫ eSec G := by
  show eSec (thickObj R I e G) ≫ pullback.fst G.hom (thick R I e) = _
  simp [eSec]
  rw [pullback.lift_fst, ← Category.assoc, ← pullback.condition, Category.comp_id]

omit [IsDomain R] in
theorem mono_fstG (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))

theorem eSec_pG {D : DegPre R} {e : ℕ} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (g : GtCoord I D e G) :
    eSec (thickObj R I e G) ≫ g.pG.left = thick R I e ≫ eSec D.P.A := by
  have := g.q_hom
  have h : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (·.left) (IsMonHom.one_hom g.q)
  rw [← eSec_fstG I e D.P.A, ← h, Category.assoc]
  rfl

end Geometry

end UnifPullRig

open UnifPullRig ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem unifPull_rig_compat : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc : G' ≅ (Over.pullback (specOf φ)).obj G), I.map φ ≤ I' → IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (L' : RigLB G') (wL : LB.Iso L'.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom (specOf φ)))) (he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) = specOf φ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (specOf φ) he U.LG.L U.LG.rig) → ∀ (gt' : ∀ e : ℕ, GtCoord I' D'.toPre e G') (w' : ∀ e : ℕ, LB.Iso (L'.L.pull (fstG I' e G').left) (D'.toPre.P.L.pull (gt' e).pG.left)), (∀ e, (w' e).IsGen) → (∀ e, thickMap R' I' e G' ≫ (gt' (e + 1)).pG.left = (gt' e).pG.left) → (∀ e : ℕ, ∃ (h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left), h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ∧ ((gt' e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (gt' e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (gt' e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((gt' e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : L'.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((gt' e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (gt' e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫ pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e G').left (r z) ∈ L'.L.U jL' → Geo.Tor.gw hD.w (r ≫ (gt' e).pG.left) z jM jM' * Geo.Tor.gw (w' e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → (∀ (e : ℕ) (p : (PUnit → D'.toPre.P.L.ι) × (PUnit → L'.L.ι)) (V : (Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1)))).Opens) (h₁ : V ≤ eSec (thickObj R' I' e G') ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' e).pG.left).U p.1 ⊓ (L'.L.pull (fstG I' e G').left).U p.2)) (h₂ : V ≤ thick R' I' e ⁻¹ᵁ (L'.L.pull (eSec G')).U p.2) (h₃ : V ≤ thick R' I' e ⁻¹ᵁ (D'.toPre.P.L.pull (eSec D'.toPre.P.A)).U p.1), res h₁ (pullU (eSec (thickObj R' I' e G')) _ ((w' e).s p)) * res h₂ (pullU (thick R' I' e) _ (L'.rig.s p.2)) = res h₃ (pullU (thick R' I' e) _ (D'.toPre.rig.s p.1))) ∧ (∀ (e : ℕ) (p : (PUnit → D'.toPre.P.L.ι) × (PUnit → L'.L.ι)) (V : (thickObj R' I' e G').left.Opens) (h₁ : V ≤ thickMap R' I' e G' ⁻¹ᵁ ((D'.toPre.P.L.pull (gt' (e + 1)).pG.left).U p.1 ⊓ (L'.L.pull (fstG I' (e + 1) G').left).U p.2)) (h₂ : V ≤ (D'.toPre.P.L.pull (gt' e).pG.left).U p.1 ⊓ (L'.L.pull (fstG I' e G').left).U p.2), res h₁ (pullU (thickMap R' I' e G') _ ((w' (e + 1)).s p)) = res h₂ ((w' e).s p)) := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc _ _ U L' wL he _ hrig gt' w' _ hq H
  have PL := (maps_iff wL _ (fun _ => eSec G) _ L'.rig U.LG.rig (specOf φ) _
    (rigPull_le (G' := G') (G := G) _ (specOf φ) he U.LG.L) (fun _ => rfl)).1 hrig
  have PM := (maps_iff hD.w _ (fun _ => eSec D.toPre.P.A) _ D'.toPre.rig D.toPre.rig (specOf φ) _
    (rigPull_le (G' := D'.toPre.P.A) (G := D.toPre.P.A) _ (specOf φ) hD.he D.toPre.P.L) (fun _ => rfl)).1 hD.w_rig
  choose h hF hE Q using H
  refine ⟨fun e => ?_, fun e => ?_⟩
  · have := mono_fstG I e G
    have hσ : (eSec (thickObj R' I' e G') ≫ h e ≫ (thickObj R I e G).hom) ≫ thick R I e =
        thick R' I' e ≫ specOf φ := by
      have c : (thickObj R I e G).hom ≫ thick R I e = (fstG I e G).left ≫ G.hom :=
        pullback.condition.symm
      have a := eSec_fstG I' e G'
      have b := eSec_hom G
      calc _ = eSec (thickObj R' I' e G') ≫ (h e ≫ (fstG I e G).left) ≫ G.hom := by
            simp only [Category.assoc, c]
        _ = (eSec (thickObj R' I' e G') ≫ (fstG I' e G').left) ≫
              (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ≫ G.hom := by
            rw [hF e]; simp only [Category.assoc]
        _ = thick R' I' e ≫ (eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)) ≫ G.hom := by
            rw [a]; simp only [Category.assoc]
        _ = thick R' I' e ≫ specOf φ := by
            rw [he, Category.assoc, b]; exact congrArg _ (Category.comp_id _)
    have hε : eSec (thickObj R' I' e G') ≫ h e =
        (eSec (thickObj R' I' e G') ≫ h e ≫ (thickObj R I e G).hom) ≫ eSec (thickObj R I e G) := by
      rw [← cancel_mono (fstG I e G).left, Category.assoc, hF e, ← Category.assoc, eSec_fstG,
        Category.assoc, he, Category.assoc _ (eSec (thickObj R I e G)), eSec_fstG]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ eSec G) hσ.symm).trans
        (Category.assoc _ _ _))
    exact rigAlong_of_square U.LG.isLB D.toPre.P.isLB (Q e) (U.w_rig e) PL PM (eSec_fstG I e G)
      (eSec_pG I (U.gt e)) (eSec_fstG I' e G') (eSec_pG I' (gt' e)) (hF e) (hE e).1 hε hσ
  · have := mono_fstG I (e + 1) G
    have hm : thickMap R' I' e G' ≫ h (e + 1) = h e ≫ thickMap R I e G := by
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, hF (e + 1), ← Category.assoc,
        thickMap_fstG, Category.assoc, thickMap_fstG, hF e]
    exact compatAlong_of_square U.LG.isLB D.toPre.P.isLB (Q e) (Q (e + 1)) (U.w_compat e)
      (thickMap_fstG I e G) (U.gt_q e) (thickMap_fstG I' e G') (hq e) (hF e) (hE e).1 hm

end GlobalTheory
