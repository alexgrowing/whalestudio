import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section

namespace GlobalTheory.FullMove

theorem isThetaPt_iso {S : Scheme.{0}} {P P' : PolAV S} (φ : P.A ≅ P'.A) [IsMonHom φ.hom]
    (hw : LBIso P.L (P'.L.pull φ.hom.left)) {T : Over S} {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    (hk : ∀ i, x i ^ (k ^ 2) = 1) {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P k x v) :
    IsThetaPt P' k (fun i => x i ≫ φ.hom) v := by
  refine ⟨H.1, H.2.1, fun p => ?_⟩
  obtain ⟨V, hV, Q⟩ := H.2.2 p
  refine ⟨V, hV, ?_⟩
  have hk' : ∀ i, (overResι V ≫ x i) ^ (k ^ 2) = 1 := fun i => by
    rw [← MonObj.comp_pow, hk, MonObj.comp_one]
  have Q' := GlobalTheory.ThetaPtUp.isThetaPtOver_up (T := overRes V) (T₀ := overRes V) (𝟙 (overRes V).left)
    (Geo.Tor.isGrpPullback_of_iso φ) hw ((Category.id_comp _).trans (Category.comp_id _).symm)
    (x₀ := fun i => overResι V ≫ x i ≫ φ.hom)
    (fun i => (Category.id_comp _).trans (by rw [← Category.assoc]; rfl)) hk' Q
  rw [IsIso.inv_id] at Q'
  exact Q'

def tateMap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (I : TateIso D k Q act e) (F : Q ≃* Q')
    (ha : ∀ c x, F (act c x) = act' c (F x))
    (he : ∀ n x y c, x ^ n = 1 → y ^ n = 1 → e n x y c → e' n (F x) (F y) c) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev n a := F (I.ev n a)
  add n a b := by rw [I.add, map_mul]
  lin n c a := by rw [I.lin, ha]
  ker n hn a := by rw [F.map_eq_one_iff, I.ker n hn]
  onto n hn x := by
    obtain ⟨y, rfl⟩ := F.surjective x
    rw [← map_pow, F.map_eq_one_iff, I.onto n hn]
    exact exists_congr fun a => F.injective.eq_iff.symm
  tower n m hn hm a := by rw [← map_pow, I.tower n m hn hm]
  isom n hn a b := he n _ _ _ ((I.onto n hn _).2 ⟨a, rfl⟩) ((I.onto n hn _).2 ⟨b, rfl⟩) (I.isom n hn a b)

def ptEquiv {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] (φ : A ≅ A') [IsMonHom φ.hom] (T : Over S) :
    (T ⟶ A) ≃* (T ⟶ A') where
  toFun x := x ≫ φ.hom
  invFun y := y ≫ φ.inv
  left_inv x := by simp
  right_inv y := by simp
  map_mul' := map_mul (IsMonHom.monoidHom φ.hom T)

theorem exists_tateIso_move : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (K : Type) [Field K] [IsAlgClosed K] (o o' : Full D K) (φ : o.P.A ≅ o'.P.A), IsPolIso o.P o'.P φ → (letI := H.starRing; ∀ x, o.oa.act x ≫ φ.hom = φ.hom ≫ o'.oa.act x) → ∃ I' : (letI := H.starRing; TateIso D K (baseOver (Sp K) ⟶ o'.P.A) (fun a g => g ≫ o'.oa.act a) (fun n g g' c => WeilIs o'.P.A o'.P.L n g g' (unitOn c))), I'.ζ = o.I.ζ ∧ (∀ M a, I'.ev M a = o.I.ev M a ≫ φ.hom) ∧ ∀ m v, o.Theta m v → Full.Theta { o' with I := I' } m v := by
  intro hL E _ _ _ H D K _ _ o o' φ ⟨hφ, t⟩ hact
  letI := H.starRing
  obtain ⟨w, hw⟩ := LBIso.symm t
  refine ⟨tateMap o.I (ptEquiv φ _) (fun c x => ?_) (fun n x y c hx hy h => ?_), rfl, fun _ _ => rfl, fun m v h => ?_⟩
  · show (x ≫ o.oa.act c) ≫ φ.hom = (x ≫ φ.hom) ≫ o'.oa.act c
    rw [Category.assoc, hact, Category.assoc]
  · exact (weilIs_iso_iff hL.globalFns hL.cube o.P o'.P φ w hw n x y hx hy _).2 h
  · exact isThetaPt_iso φ ⟨w, hw⟩ (fun a => (o.I.onto _ (pow_pos h.1.pos 2) _).2 ⟨a, rfl⟩) h

end GlobalTheory.FullMove

end
