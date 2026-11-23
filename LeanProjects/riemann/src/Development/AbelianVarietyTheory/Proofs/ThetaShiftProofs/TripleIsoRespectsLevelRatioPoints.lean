import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOfSameRatios
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFptsPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RepTransport

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LevelRespect

open GlobalTheory.FibrePull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]

theorem valR_zero {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) : valR x U 0 = 0 := by
  unfold valR
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem sval_of_zero {A : Type} [CommRing A] {X Z : Scheme.{0}} {L : LB Z} {π : X ⟶ Z} {n : ℕ} (u : SecP L π n)
    (hu : ∀ i, u.f i = 0) (x : Sp A ⟶ X) (j : L.ι) : ArcPts.sval u x j = 0 :=
  (congrArg (valR x _) (hu fun _ => j)).trans (valR_zero _ _)

section One
variable {S : Scheme.{0}} {t : SAB H S} {F : Type} [Field F] {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V}
  {I : ℕ → Type} {φ : ∀ j, I j → V → F} {y : Sp F ⟶ S}

omit [StarRing (𝓞 E)] in
theorem fib_fst (a : Over.mk y ⟶ t.G) : fib a ≫ pullback.fst t.G.hom y = a.left := pullback.lift_fst _ _ _

omit [StarRing (𝓞 E)] in

theorem sval_eq_sum (Θ : FPts act t y φ) {k : ℕ} (hk : 1 ≤ k) (s : SecP t.PP.L (pullback.fst t.G.hom y) k) {n : ℕ}
    (r : Fin n → F) (i : Fin n → I k) (hs : ∀ v, HasVal s (fib (Θ.x v)) (Θ.τ v) (∑ a, r a * φ k (i a) v))
    (q : Over.mk y ⟶ t.G) (j : t.PP.L.ι) (hj : ⊤ ≤ q.left ⁻¹ᵁ t.PP.L.U j) :
    ArcPts.sval s (fib q) j = ∑ a, r a * ArcPts.sval (Θ.sig k (i a)) (fib q) j := by
  have key : ∀ (q : Over.mk y ⟶ t.G) (j : t.PP.L.ι), ⊤ ≤ (fib q ≫ pullback.fst t.G.hom y) ⁻¹ᵁ t.PP.L.U j →
      ArcPts.sval (FibreFrame.comb (pullback.snd t.G.hom y) (Fin.cons (-1) r : Fin (n + 1) → F)
        (Fin.cons s fun a => Θ.sig k (i a)) : SecP t.PP.L (pullback.fst t.G.hom y) k) (fib q) j =
      ∑ a, r a * ArcPts.sval (Θ.sig k (i a)) (fib q) j - ArcPts.sval s (fib q) j := fun q j hj => by
    rw [FibreFrame.sval_comb _ _ _ (RingHom.id F) (fib q)
      ((pullback.lift_snd _ _ _).trans (Spec.map_id _).symm) hj, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, RingHom.id_apply]
    ring
  have h0 := Θ.sep k hk _ fun v j hj => by
    rw [key _ j hj, hs v j hj, Finset.sum_mul, MulZeroClass.zero_mul, sub_eq_zero]
    exact Finset.sum_congr rfl fun a _ => by rw [Θ.val k hk (i a) v j hj, _root_.mul_assoc]
  have e := key q j (by rw [fib_fst]; exact hj)
  rw [sval_of_zero _ h0] at e
  exact (sub_eq_zero.1 e.symm).symm

omit [StarRing (𝓞 E)] in

theorem sval_lev (Θ : FPts act t y φ) {k : ℕ} (hk : 1 ≤ k) {p : Over.mk y ⟶ t.G} {ψ : I k → V → F}
    (hp : Θ.Lev k p ψ) (s : SecP t.PP.L (pullback.fst t.G.hom y) k) {n : ℕ}
    (r : Fin n → F) (i : Fin n → I k) (hs : ∀ v, HasVal s (fib (Θ.x v)) (Θ.τ v) (∑ a, r a * φ k (i a) v))
    (i₀ : I k) (z : V) (j : t.PP.L.ι) (hj : ⊤ ≤ (Θ.x z * p).left ⁻¹ᵁ t.PP.L.U j) :
    ArcPts.sval s (fib (Θ.x z * p)) j * ψ i₀ z =
      ArcPts.sval (Θ.sig k i₀) (fib (Θ.x z * p)) j * ∑ a, r a * ψ (i a) z := by
  rw [sval_eq_sum Θ hk s r i hs _ j hj, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [_root_.mul_assoc, hp.2.2 (i a) i₀ z j hj]; ring

end One

theorem level_eq (h₁ : Out.Laws) (h₂ : Out.Laws2) {D : Datum H} {l : Level H} {B : Type} [CommRing B] {bb : Base l B}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l bb s) {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' o.t f)
    (w : LB.Iso t'.PP.L (o.t.PP.L.pull m.φ)) (hw : w.IsGen) {F : Type} [Field F] [IsAlgClosed F] [CharZero F]
    {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {φ : ∀ j, I j → V → F} (y' : Sp F ⟶ S')
    (y : Sp F ⟶ S) (hy : y' ≫ f = y) (Θ' : FPts act t' y' φ) (Θ : FPts act o.t y φ) {k : ℕ} (hk : 1 ≤ k)
    {ψ : I k → V → F} {p' : Over.mk y' ⟶ t'.G} {p : Over.mk y ⟶ o.t.G}
    (rel : ∀ v, (Θ'.x v).left ≫ m.φ = (Θ.x v).left ∧ ∀ j j',
        ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (o.t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') →
        Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j')
    (l' : Θ'.Lev k p' ψ) (l₀ : Θ.Lev k p ψ) : p'.left ≫ m.φ = p.left := by
  subst hy
  have hL := o.t.PP.isLB
  have hL' := t'.PP.isLB
  let ρ : (Over.mk y' ⟶ t'.G) →* (Over.mk (y' ≫ f) ⟶ o.t.G) := pushHom m.cart (Over.mk y')
  have ρl : ∀ x, (ρ x).left = x.left ≫ m.φ := fun _ => rfl
  have hx : ∀ v, ρ (Θ'.x v) = Θ.x v := fun v => Over.OverMorphism.ext (rel v).1
  have sq : IsPullback (pullback.fst t'.G.hom y' ≫ m.φ) (pullback.snd t'.G.hom y') o.t.G.hom (y' ≫ f) :=
    (IsPullback.of_hasPullback t'.G.hom y').paste_horiz m.cart.1
  let h : pullback t'.G.hom y' ⟶ pullback o.t.G.hom (y' ≫ f) := sq.isoPullback.hom
  have hp : pullback.fst t'.G.hom y' ≫ m.φ = h ≫ pullback.fst o.t.G.hom (y' ≫ f) := sq.isoPullback_hom_fst.symm
  have fh : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ h = fib (ρ a) := fun a => pullback.hom_ext
    (by rw [Category.assoc, ← hp, ← Category.assoc, fib_fst]; exact (pullback.lift_fst _ _ _).symm)
    (by rw [Category.assoc, sq.isoPullback_hom_snd]
        exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)
  have hv : ∀ {a : SecP t'.PP.L (pullback.fst t'.G.hom y') k} {b : SecP o.t.PP.L (pullback.fst o.t.G.hom (y' ≫ f)) k},
      TransportedAlt w a b h → ∀ v c, HasVal a (fib (Θ'.x v)) (Θ'.τ v) c ↔ HasVal b (fib (Θ.x v)) (Θ.τ v) c := fun T v c => by
    rw [← hx v, ← fh]
    exact T.hasVal_iff hL hL' hp _ (by
      rw [fib_fst]; exact fun j j' hj hj' => (rel v).2 j j' ((le_div_iff _ j j').2 ⟨hj, hj'⟩)) c
  obtain ⟨-, i₀, i₁, hgood, z₀, hz₀⟩ := l₀.2.1
  have main := LevelUnique.torsion_eq_of_same_ratios h₁ h₂ E H D l B bb S s o F (y' ≫ f) V Θ.x k (ρ p') p
    (fun z => ψ i₀ z ≠ 0) (Θ.sig k i₁) hk (by rw [← map_pow, l'.1, map_one]) l₀.1
    (fun n hn u hu => Θ.sep n hn u fun v j hj => by
      rw [MulZeroClass.zero_mul]; exact hu v j (by rwa [fib_fst] at hj))
    (by
      by_contra hne
      push_neg at hne
      obtain ⟨j, hj⟩ := exists_chart_pt hL (Θ.x z₀).left
      have e := Θ.val k hk i₁ z₀ j (by rw [fib_fst]; exact hj)
      rw [sval_of_zero _ hne] at e
      exact mul_ne_zero hz₀ (pow_ne_zero _ ((Θ.frm z₀).1 j hj).ne_zero) e.symm)
    (fun v j hj hne => hgood v fun h0 => hne (by
      rw [Θ.val k hk i₁ v j (by rw [fib_fst]; exact hj), h0, MulZeroClass.zero_mul]))
    (fun z hz t₁ t₂ j j₂ hj hj₂ => by
      obtain ⟨j', hj'⟩ := exists_chart_pt hL' (Θ'.x z * p').left
      have hj₁ : ⊤ ≤ ((fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') ≫ m.φ) ⁻¹ᵁ o.t.PP.L.U j := by
        rw [fib_fst, ← ρl, map_mul, hx]; exact hj
      have hj₃ : ⊤ ≤ (fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') ⁻¹ᵁ t'.PP.L.U j' := by rw [fib_fst]; exact hj'
      have both : ∀ b : SecP o.t.PP.L (pullback.fst o.t.G.hom (y' ≫ f)) k, ∃ c : F,
          ArcPts.sval b (fib (Θ.x z * ρ p')) j * ψ i₀ z =
            wv w (fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') j j' ^ k *
              ArcPts.sval (Θ'.sig k i₀) (fib (Θ'.x z * p')) j' * c ∧
          ArcPts.sval b (fib (Θ.x z * p)) j₂ * ψ i₀ z = ArcPts.sval (Θ.sig k i₀) (fib (Θ.x z * p)) j₂ * c := fun b => by
        obtain ⟨n, r, i, hi⟩ := Θ.span k hk b
        obtain ⟨a, ha⟩ := ConstFam.exists_secThrough (K := Fin 1) (φ' := fun _ => pullback.fst t'.G.hom y')
          hw hL hL' (fun _ => hp) b
        refine ⟨∑ a, r a * ψ (i a) z, ?_, sval_lev Θ hk l₀ b r i hi i₀ z j₂ hj₂⟩
        rw [← hx, ← map_mul, ← fh, TransportedAlt.sval_eq hp ha _ hj₁ hj₃, _root_.mul_assoc,
          sval_lev Θ' hk l' a r i (fun v => (hv ha v _).2 (hi v)) i₀ z j' hj', _root_.mul_assoc]
      obtain ⟨c₁, a₁, b₁⟩ := both t₁
      obtain ⟨c₂, a₂, b₂⟩ := both t₂
      refine mul_right_cancel₀ (mul_ne_zero hz hz) ?_
      rw [_root_.mul_mul_mul_comm, a₁, b₂, _root_.mul_mul_mul_comm (ArcPts.sval t₂ _ j), a₂, b₁]
      ring)
  exact congrArg (fun q => q.left) main

theorem level_pt_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ) (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)) (k : ℕ) (ψ : I k → V → F) (p₁ : Over.mk (𝟙 (Sp F)) ⟶ o₁.t.G) (p₂ : Over.mk (𝟙 (Sp F)) ⟶ o₂.t.G), 1 ≤ k → w.IsGen → (∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j') → Θ₁.Lev k p₁ ψ → Θ₂.Lev k p₂ ψ → p₁.left ≫ m.φ = p₂.left := by
  intro h₁ h₂ E _ _ _ H _ D l B _ bb F _ _ _ V _ act I φ s o₁ o₂ Θ₁ Θ₂ m w k ψ p₁ p₂ hk hw rel l₁ l₂
  exact level_eq h₁ h₂ o₂ m w hw (𝟙 _) (𝟙 _) (Category.id_comp _) Θ₁ Θ₂ hk rel l₁ l₂

end GlobalTheory.LevelRespect
