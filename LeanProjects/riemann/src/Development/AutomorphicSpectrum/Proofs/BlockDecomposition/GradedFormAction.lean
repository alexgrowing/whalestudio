import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

section Abstract

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

def mulSq (a b : IdF A) (T : C) (y : A.obj T) : sqM a b T →ₗ[R] sqM a b T where
  toFun x := ⟨Ideal.Quotient.mk _ y * x.1, Ideal.mul_mem_left ((a.S T).map (Ideal.Quotient.mk (b.S T))) _ x.2⟩
  map_add' x x' := Subtype.ext (mul_add _ _ _)
  map_smul' c x := Subtype.ext (mul_smul_comm _ _ _)

def mulMor (a b c : IdF A) (y : ∀ T : C, A.obj T)
    (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (A.map φ).hom (y T) ∈ c.S T')
    (hc : ∀ (T : C) {v w : A.obj T}, v ∈ c.S T → w ∈ a.S T → v * w ∈ b.S T) :
    CH.Mor (sq a b) (sq a b) (RingHom.id R) where
  G := 𝟭 C
  τ T := mulSq a b T (y T)
  nat {T T'} φ x := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
    have key : ∀ w : A.obj T, w ∈ a.S T → Ideal.Quotient.mk (b.S T') (y T') * Ideal.Quotient.mk (b.S T') ((A.map φ).hom w) =
        Ideal.Quotient.mk (b.S T') ((A.map φ).hom (y T * w)) := by
      intro w hw
      rw [← map_mul, map_mul (A.map φ).hom, Ideal.Quotient.eq, ← sub_mul]
      exact hc _ (hy φ) (a.map_mem φ hw)
    exact Subtype.ext (key w hw)

end Abstract

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem sub_mem_of_lift {W : X.Opens} {T T' : Thick (LL q)} (φ : T ⟶ T') (h : InU W T) (h' : InU W T') (f : Γ(X, W))
    (v : T.B) (v' : T'.B) (hv : Ideal.Quotient.mk T.J v = ev T h f) (hv' : Ideal.Quotient.mk T'.J v' = ev T' h' f) :
    v' - φ.φ v ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [hv', ev_nat φ h h', ← hv]
  rfl

theorem lft_mul_sub {W : X.Opens} (T : Thick (LL q)) (h : InU W T) (f g : Γ(X, W)) :
    lft W T f * lft W T g - lft W T (f * g) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [map_mul, lft_spec T h, lft_spec T h, lft_spec T h, map_mul]

theorem J_mul_sFil (P : ObjectProperty (Thick (LL q))) (r : ℕ) (T : P.FullSubcategory) {v w : (sP P).A.obj T}
    (hv : v ∈ (sP P).J.S T) (hw : w ∈ (sFil P r).S T) : v * w ∈ (sFil P ((r : ℤ) + 1)).S T := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have h1 : v ∈ (sFil P 1).S T := by
    have e := hF.one T
    rw [e]
    exact hv
  have := hF.mul 1 r T (x := v) (y := w) h1 hw
  have e : (((1 + r : ℕ)) : ℤ) = (r : ℤ) + 1 := by push_cast; ring
  rwa [e] at this

def mulZ {W : X.Opens} (P : ObjectProperty (Thick (LL q))) (hP : ∀ T, P T → InU W T) (r : ℕ) (z : Γ(X, W)) :
    CH.Mor (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (sq (sFil P r) (sFil P ((r : ℤ) + 1))) (RingHom.id O) :=
  mulMor (sFil P r) (sFil P ((r : ℤ) + 1)) (sP P).J (fun T => lft W T.obj z)
    (fun {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) z _ _
      (lft_spec _ (hP _ T.property) z) (lft_spec _ (hP _ T'.property) z))
    (fun T _ _ hv hw => J_mul_sFil P r T hv hw)

theorem units_mul_relation_rearrange_commRing {S : Type} [CommRing S] (y w l l' : S) : y * (w * l) - w * l' = (y * l - l') * w := by ring

theorem stAct : StAct := by
  intro O _ X q W P hP r z
  refine ⟨((mulZ P hP r z).pull r).toAddMonoidHom, ?_⟩
  intro d t u hu x c hc
  obtain ⟨f, hf, rfl, hfs⟩ := hc
  refine ⟨(mulZ P hP r z).pullC r f, ?_, rfl, ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · intro s
    have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
    let uu : Fin d → ∀ T : P.FullSubcategory, (sP P).A.obj T := fun i T => u i T.obj
    have hl : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'), uu i T' - ((sP P).A.map φ).hom (uu i T) ∈ (sP P).J.S T' :=
      fun i {T T'} φ => sub_mem_of_lift φ.hom (hP _ T.property) (hP _ T'.property) (t i) _ _
        (hu i _ (hP _ T.property)) (hu i _ (hP _ T'.property))
    change Ideal.Quotient.mk _ (show (sP P).A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj z) *
      (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f s).1 = _
    rw [hfs s, ← map_mul, Ideal.Quotient.eq, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun I _ => ?_
    have hw := wz_mem hF uu hl I.1 s
    have hd := lft_mul_sub _ (hP _ (s.obj (Fin.last r)).property) z (x I)
    have := J_mul_sFil P r _ hd hw
    have e := units_mul_relation_rearrange_commRing (S := (sP P).A.obj (s.obj (Fin.last r)))
      (lft W (s.obj (Fin.last r)).obj z) (wz uu I.1 s) (lft W (s.obj (Fin.last r)).obj (x I))
      (lft W (s.obj (Fin.last r)).obj (z * x I))
    exact Eq.mpr (congrArg (fun v => v ∈ (sFil P ((r : ℤ) + 1)).S (s.obj (Fin.last r))) e) this

end GlobalTheory.CompanionTheory.GrForm
