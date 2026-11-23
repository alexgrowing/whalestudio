import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELOfTmap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
namespace GlobalTheory.ZM
open GlobalTheory.SiegelRingChange GlobalTheory.SiegelPullComp

variable {o : Type} [CommRing o] {S : Scheme.{0}} {g h k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}

theorem dense_generic_of_flat [IsDomain o] (s : S ⟶ Sp o) [Flat s] : Dense {x : S | (s x).asIdeal = ⊥} := by
  intro x
  obtain ⟨y, hy⟩ := S.affineCover.covers x
  have hcomp : Flat (S.affineCover.f (S.affineCover.idx x) ≫ s) :=
    MorphismProperty.comp_mem _ _ _ inferInstance ‹Flat s›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (S.affineCover.f (S.affineCover.idx x) ≫ s)
  have hfl : φ.hom.Flat := by
    rw [← HasRingHomProperty.Spec_iff (P := @Flat), hφ]
    exact hcomp
  have hsp : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o) ⤳ PrimeSpectrum.comap φ.hom y :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal o) ≤ _ from bot_le)
  obtain ⟨y', hy'1, hy'2⟩ := RingHom.Flat.generalizingMap_comap hfl hsp
  have hφy := congrArg (fun m => (m y').asIdeal) hφ
  have hmem : S.affineCover.f (S.affineCover.idx x) y' ∈ {x : S | (s x).asIdeal = ⊥} := by
    change ((S.affineCover.f (S.affineCover.idx x) ≫ s) y').asIdeal = ⊥
    refine Eq.trans ?_ (congrArg PrimeSpectrum.asIdeal hy'2)
    exact hφy.symm
  have h₁ : S.affineCover.f (S.affineCover.idx x) y' ⤳ S.affineCover.f (S.affineCover.idx x) y :=
    hy'1.map (S.affineCover.f (S.affineCover.idx x)).continuous
  have h₂ : S.affineCover.f (S.affineCover.idx x) y ⤳ x := by rw [hy]
  exact (h₁.trans h₂).mem_closed isClosed_closure (subset_closure hmem)

theorem dense_generic_spMap {O : Type} [CommRing O] [IsDomain O] (β : o →+* O) (hβ : Function.Injective β) :
    Dense {x : Sp O | (spMap β x).asIdeal = ⊥} := by
  intro x
  have hη : (show ↥(Sp O) from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O)) ⤳ x :=
    (PrimeSpectrum.le_iff_specializes _ _).1 (show (⊥ : Ideal O) ≤ x.asIdeal from bot_le)
  refine hη.mem_closed isClosed_closure (subset_closure ?_)
  change (PrimeSpectrum.comap β ⟨⊥, Ideal.isPrime_bot⟩).asIdeal = ⊥
  exact Ideal.comap_bot_of_injective β hβ

namespace SFam
variable {ζ : o}

theorem hom_ext (F : SFam h k ζ) {s' : S ⟶ Sp o} (c : SiegPre h k ζ s') (f f' : S ⟶ F.X)
    (hs : f ≫ F.s = f' ≫ F.s) (h₁ : SiegPB c F.univ f) (h₂ : SiegPB c F.univ f') : f = f' := by
  apply hom_ext_of_fromSpecStalk
  intro x
  obtain ⟨c', hc'⟩ := (siegPre_pullback h k o ζ S (Spec (S.presheaf.stalk x)) s' (S.fromSpecStalk x ≫ s')
    (S.fromSpecStalk x) c rfl).1
  exact F.inj (S.presheaf.stalk x) _ _ _ c' (by simp only [Category.assoc, hs]) (pb_comp h₁ hc') (pb_comp h₂ hc')

theorem existsUnique (F : SFam h k ζ) {s' : S ⟶ Sp o} (c : SiegPre h k ζ s') (hr : IsReduced S)
    (hd : Dense {x : S | (s' x).asIdeal = ⊥}) (hc : c.Principal) :
    ∃! f : S ⟶ F.X, f ≫ F.s = s' ∧ SiegPB c F.univ f := by
  obtain ⟨f, hf, hpb⟩ := F.rep S s' c hr hd hc
  exact ⟨f, ⟨hf, hpb⟩, fun f' hf' => F.hom_ext c f' f (hf'.1.trans hf.symm) hf'.2 hpb⟩

theorem exists_point (F : SFam h k ζ) {O : Type} [CommRing O] [IsDomain O] (β : o →+* O) (hβ : Function.Injective β)
    (c : SiegPre h k ζ (spMap β)) (hc : c.Principal) : ∃ x : Sp O ⟶ F.X, x ≫ F.s = spMap β ∧ SiegPB c F.univ x := by
  obtain ⟨f, hf, hpb⟩ := F.rep (Sp O) (spMap β) c inferInstance (dense_generic_spMap β hβ) hc
  exact ⟨f, hf, hpb⟩

theorem nonempty (F : SFam h k ζ) {O : Type} [CommRing O] [IsDomain O] (β : o →+* O) (hβ : Function.Injective β)
    (c : SiegPre h k ζ (spMap β)) (hc : c.Principal) : Nonempty F.X := by
  obtain ⟨x, -, -⟩ := F.exists_point β hβ c hc
  exact ⟨x (show ↥(Sp O) from (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum O))⟩

theorem isReduced_and_dense [IsDomain o] (F : SFam h k ζ) : IsReduced F.X ∧ Dense {x : F.X | (F.s x).asIdeal = ⊥} := by
  have := F.smooth
  have : Smooth F.s := SmoothOfRelativeDimension.smooth (n := h * (h + 1) / 2) (f := F.s)
  have : IsReduced F.X := isReduced_of_smooth_of_isReduced F.s
  exact ⟨inferInstance, dense_generic_of_flat F.s⟩

theorem exists_iso [IsDomain o] (F F' : SFam h k ζ) :
    ∃ e : F.X ≅ F'.X, e.hom ≫ F'.s = F.s ∧ SiegPB F.univ F'.univ e.hom := by
  obtain ⟨hr, hd⟩ := F.isReduced_and_dense
  obtain ⟨hr', hd'⟩ := F'.isReduced_and_dense
  obtain ⟨f, hf, hpf⟩ := F'.rep F.X F.s F.univ hr hd F.princ
  obtain ⟨g, hg, hpg⟩ := F.rep F'.X F'.s F'.univ hr' hd' F'.princ
  have e₁ : f ≫ g = 𝟙 _ :=
    F.hom_ext F.univ _ _ (by rw [Category.assoc, hg, hf, Category.id_comp]) (pb_comp hpg hpf) (pb_id _)
  have e₂ : g ≫ f = 𝟙 _ :=
    F'.hom_ext F'.univ _ _ (by rw [Category.assoc, hf, hg, Category.id_comp]) (pb_comp hpf hpg) (pb_id _)
  exact ⟨⟨f, g, e₁, e₂⟩, hf, hpf⟩

theorem exists_baseChange (F : SFam h k ζ) {B : Type} [CommRing B] {ζ' : B} (j : o →+* B) (hi : Function.Injective j)
    (hj : j ζ = ζ') : ∃ (F' : SFam h k ζ') (π : F'.X ⟶ F.X),
      IsPullback π F'.s F.s (spMap j) ∧ SiegPB F'.univ F.univ π := by
  have sq := IsPullback.of_hasPullback F.s (spMap j)
  have hrc := siegPre_pull_ringChange h k o B ζ ζ' j F.X (pullback F.s (spMap j)) F.s
    (pullback.snd F.s (spMap j)) (pullback.fst F.s (spMap j)) hj pullback.condition
  obtain ⟨u, hu⟩ := hrc.1 F.univ
  refine ⟨SFam.mk (pullback F.s (spMap j)) (pullback.snd F.s (spMap j)) ?_
    (isQProjOver_of_isPullback_spMap j sq F.qproj) u (hrc.2.1 F.univ u hu F.princ) ?_ ?_,
    pullback.fst F.s (spMap j), sq, hu⟩
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange (n := h * (h + 1) / 2)).of_isPullback sq F.smooth
  · intro T t c hr hd hc
    have hd' : Dense {x : T | ((t ≫ spMap j) x).asIdeal = ⊥} := by
      refine hd.mono fun x hx => ?_
      have hx' : (t x).asIdeal = ⊥ := hx
      change Ideal.comap j (t x).asIdeal = ⊥
      exact (congrArg (Ideal.comap j) hx').trans (Ideal.comap_bot_of_injective j hi)
    obtain ⟨f₀, hf₀, hpb⟩ := F.rep T (t ≫ spMap j) (down j hj c) hr hd' hc
    refine ⟨pullback.lift f₀ t hf₀, pullback.lift_snd _ _ _, ?_⟩
    have hpb' : SiegPB c F.univ (pullback.lift f₀ t hf₀ ≫ pullback.fst F.s (spMap j)) := by
      rw [pullback.lift_fst]
      exact hpb
    exact pb_cancel hu hpb'
  · intro R _ _ x y t c hxy hx hy
    refine pullback.hom_ext ?_ hxy
    have e : (x ≫ pullback.fst F.s (spMap j)) ≫ F.s = (y ≫ pullback.fst F.s (spMap j)) ≫ F.s := by
      simp only [Category.assoc, pullback.condition, reassoc_of% hxy]
    exact F.inj R _ _ (t ≫ spMap j) (down j hj c) e (pb_comp hu hx) (pb_comp hu hy)

theorem siegRep {p M : ℕ} (F : SFam h M (zetaZP p M))
    (sm : SmoothOfRelativeDimension (h * (h + 1) / 2) F.s) (qc : QuasiCompact F.s) (pr : F.univ.Principal) (pts unr) :
    GlobalTheory.Models.SiegRep (⟨F.X, F.s, sm, qc, F.univ, pr, pts, unr⟩ : SiegelFamily h p M) := by
  unfold GlobalTheory.Models.SiegRep
  refine ⟨F.qproj, fun T t c hr _ hfl hc => ?_⟩
  exact F.existsUnique c hr (dense_generic_of_flat t) hc

end SFam

theorem SFam.exists_sRep_siegRep {p M : ℕ} (hM : M ≠ 0) (F : SFam h M (zetaZP p M)) (Ag : SiegelFamily h p M)
    (H : SRep Ag) : ∃ Ag' : SiegelFamily h p M, SRep Ag' ∧ GlobalTheory.Models.SiegRep Ag' := by
  obtain ⟨hsep, hrep⟩ := H
  obtain ⟨hr, hd⟩ := F.isReduced_and_dense
  have := Ag.smooth
  have : Smooth Ag.s := SmoothOfRelativeDimension.smooth (n := h * (h + 1) / 2) (f := Ag.s)
  have : IsReduced Ag.X := isReduced_of_smooth_of_isReduced Ag.s
  obtain ⟨f, hf, hpf⟩ := hrep F.X F.s F.univ hr hd F.princ
  obtain ⟨g, hg, hpg⟩ := F.rep Ag.X Ag.s Ag.univ inferInstance (dense_generic_of_flat Ag.s) Ag.princ
  have hfg : f ≫ g = 𝟙 _ :=
    F.hom_ext F.univ _ _ (by rw [Category.assoc, hg, hf, Category.id_comp]) (pb_comp hpg hpf) (pb_id _)
  have : IsSeparated (g ≫ F.s) := by rw [hg]; exact hsep
  have : IsSeparated g := IsSeparated.of_comp g F.s
  have : IsClosedImmersion (f ≫ g) := by rw [hfg]; infer_instance
  have : IsClosedImmersion f := IsClosedImmersion.of_comp f g
  have := Ag.qc
  have qc : QuasiCompact F.s := by rw [← hf]; infer_instance
  refine ⟨⟨F.X, F.s, F.smooth, qc, F.univ, F.princ, ?_, ?_⟩, ?_, ?_⟩
  · intro C O _ _ _ _ _ _ _ _ hu hp β o ho ha
    obtain ⟨y, hy, hpy⟩ := Ag.points C O hu hp β o ho ha
    exact ⟨y ≫ g, by rw [Category.assoc, hg, hy], pb_comp hpg hpy⟩
  · intro K _ x o h₁ h₂
    have key : ∀ (s₁ : Sp (DualNumber K) ⟶ Sp (ZP p M)) (o₁ : SiegPre h M (zetaZP p M) s₁),
        s₁ = (x ≫ f) ≫ Ag.s → SiegPB o₁ Ag.univ (x ≫ f) → SiegPB o₁ Ag.univ (constPt (x ≫ f)) →
        x ≫ f = constPt (x ≫ f) := by
      rintro s₁ o₁ rfl
      exact Ag.unram K (x ≫ f) o₁
    have hc : constPt (x ≫ f) = constPt x ≫ f := by simp only [constPt, Category.assoc]
    have e : x ≫ f = constPt x ≫ f := by
      rw [← hc]
      refine key _ o (by rw [Category.assoc, hf]) (pb_comp hpf h₁) ?_
      rw [hc]
      exact pb_comp hpf h₂
    calc x = x ≫ (f ≫ g) := by rw [hfg, Category.comp_id]
      _ = (x ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (constPt x ≫ f) ≫ g := by rw [e]
      _ = constPt x := by rw [Category.assoc, hfg, Category.comp_id]
  · exact F.sRep F.smooth qc F.princ _ _
  · exact F.siegRep F.smooth qc F.princ _ _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem PELRep.exists_point {D : Datum H} {a : J → 𝓞 E} {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La} {ρ : o}
    {t : TObj g k J b s} (R : PELRep D a bas ρ t) {K : Type} [Field K] (β : o →+* K) (hβ : Function.Injective β)
    (t' : TObj g k J b (spMap β)) (τ' : SAB H (Sp K)) (h' : IsPEL D a bas ρ t' τ') :
    ∃ x : Sp K ⟶ S, x ≫ s = spMap β ∧ TMap t' t x := by
  have hC : Function.Injective ((PowerSeries.C (R := K)).comp β) := PowerSeries.C_injective.comp hβ
  have e₁ : spMap (PowerSeries.C (R := K)) ≫ spMap β = spMap ((PowerSeries.C (R := K)).comp β) :=
    (spMap_comp' β PowerSeries.C).symm
  obtain ⟨t'', ht''⟩ := tObj_pull o g k J b (Sp K) (Sp (PowerSeries K)) (spMap β)
    (spMap ((PowerSeries.C (R := K)).comp β)) (spMap PowerSeries.C) t' e₁
  obtain ⟨τ'', hτ''⟩ := exists_isPEL_of_tmap E H D g J a bas k o b ρ (Sp K) (Sp (PowerSeries K)) (spMap β)
    (spMap ((PowerSeries.C (R := K)).comp β)) t' t'' τ' (spMap PowerSeries.C) e₁ ht'' h'
  obtain ⟨f, hf, hft⟩ := R.rep (PowerSeries K) ((PowerSeries.C (R := K)).comp β) t'' τ'' hC hτ''
  have e₂ : spMap (PowerSeries.constantCoeff (R := K)) ≫ spMap (PowerSeries.C (R := K)) = 𝟙 (Sp K) := by
    have : (PowerSeries.constantCoeff (R := K)).comp PowerSeries.C = RingHom.id K :=
      RingHom.ext fun x => PowerSeries.constantCoeff_C x
    rw [← spMap_comp', this]
    simp
  refine ⟨spMap PowerSeries.constantCoeff ≫ f, ?_, ?_⟩
  · rw [Category.assoc, hf, ← e₁, ← Category.assoc, e₂, Category.id_comp]
  · have hback : TMap t' t'' (spMap PowerSeries.constantCoeff) := by
      refine TMap.cancel ht'' ?_
      rw [e₂]
      exact TMap.refl t'
    exact TMap.comp hback hft

theorem exists_hom_of_basis {G : Type} [CommGroup G] {n : ℕ} (p : Fin n → G) :
    ∃ q : (Fin n → ℤ) → G, (∀ x y, q (x + y) = q x * q y) ∧ ∀ i, q (Pi.single i 1) = p i := by
  refine ⟨fun x => ∏ i, p i ^ x i, fun x y => ?_, fun i => ?_⟩
  · simp only [Pi.add_apply, zpow_add, Finset.prod_mul_distrib]
  · show ∏ j, p j ^ (Pi.single i (1 : ℤ) : Fin n → ℤ) j = p i
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zpow_zero])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, zpow_one]

end GlobalTheory.ZM
end
