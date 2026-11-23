import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfPullbackSectionsProportionalToCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsEmbedOfBaseChangeStableBasisStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section
namespace GlobalTheory.HomFixUniv

variable {A₀ B₀ X Z T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

theorem comb_pull (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (r : Z ⟶ X) (z : Z) (q : N.ι) (h : φ (r z) ∈ N.U q) (j : Fin mB) :
    comb a (r ≫ φ) (r ≫ p) c z q j = (r.stalkMap z).hom (comb a φ p c (r z) q j) := by
  simp only [comb, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_comp r p z ⊤ trivial, gs_comp r φ z _ h]

theorem Generates.pull {a : Fin mA → LB.Sec N} {φ : X ⟶ A₀} {p : X ⟶ T} {c : Fin mA → Fin mB → Γ(T, ⊤)}
    (hg : Generates a φ p c) (r : Z ⟶ X) : Generates a (r ≫ φ) (r ≫ p) c := by
  intro z q hz
  obtain ⟨j, hj⟩ := hg (r z) q hz
  exact ⟨j, by rw [comb_pull a φ p c r z q hz]; exact hj.map _⟩

theorem Proport.pull {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {φ : X ⟶ A₀} {p : X ⟶ T} {Ψ : X ⟶ B₀}
    {c : Fin mA → Fin mB → Γ(T, ⊤)} (hp : Proport a b φ p Ψ c) (r : Z ⟶ X) :
    Proport a b (r ≫ φ) (r ≫ p) (r ≫ Ψ) c := by
  intro z q k hq hk j j'
  rw [comb_pull a φ p c r z q hq, comb_pull a φ p c r z q hq, gs_comp r Ψ z _ hk, gs_comp r Ψ z _ hk,
    ← map_mul, ← map_mul, hp (r z) q k hq hk j j']

theorem gs_top_comp {S : Scheme.{0}} (t : T ⟶ S) (z : T) (x : Γ(S, ⊤)) :
    (t.stalkMap z).hom (gs (𝟙 S) (t z) ⊤ x) = gs (𝟙 T) z ⊤ (t.appTop x) := by
  rw [← gs_comp t (𝟙 S) z ⊤ trivial, Category.comp_id]
  have e := gs_pull (𝟙 T) t z ⊤ trivial x
  rw [Category.id_comp] at e
  exact e.symm

theorem proport_zero {S : Scheme.{0}} {a : Fin mA → LB.Sec N} {b : Fin mB → LB.Sec H} {eA : S ⟶ A₀} {eB : S ⟶ B₀}
    {uA : ∀ z : S, N.ι → (S.presheaf.stalk z)ˣ} {uB : ∀ z : S, H.ι → (S.presheaf.stalk z)ˣ}
    {α : Fin mA → Γ(S, ⊤)} {β : Fin mB → Γ(S, ⊤)} (t : T ⟶ S) (c : Fin mA → Fin mB → Γ(T, ⊤))
    (ha : ∀ i, IsVal eA uA (a i) (α i)) (hb : ∀ j, IsVal eB uB (b j) (β j)) (hn : Normal t c α β) :
    Proport a b (t ≫ eA) (𝟙 T) (t ≫ eB) c := by
  intro z q k hq hk j j'
  have hc : ∀ j, comb a (t ≫ eA) (𝟙 T) c z q j =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uA (t z) q).val := by
    intro j
    simp only [comb]
    have e : ∀ i, gs (t ≫ eA) z (N.U q) ((a i).f q) =
        gs (𝟙 T) z ⊤ (t.appTop (α i)) * (t.stalkMap z).hom (uA (t z) q).val := by
      intro i
      rw [gs_comp t eA z _ hq, ha i (t z) q hq, map_mul, gs_top_comp]
    simp only [e, hn j, gs_eq (𝟙 T) z ⊤ trivial, map_sum, map_mul, Finset.sum_mul, _root_.mul_assoc]
  have hbj : ∀ j, gs (t ≫ eB) z (H.U k) ((b j).f k) =
      gs (𝟙 T) z ⊤ (t.appTop (β j)) * (t.stalkMap z).hom (uB (t z) k).val := by
    intro j
    rw [gs_comp t eB z _ hk, hb j (t z) k hk, map_mul, gs_top_comp]
  rw [hc, hc, hbj, hbj]
  ring

end GlobalTheory.HomFixUniv

namespace GlobalTheory.HomFixUniv

theorem snd_θ {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : (snd (topS Rg) B).left ≫ θ B = 𝟙 _ := by
  have key : ∀ h : B ⟶ topS Rg, snd (topS Rg) B ≫ lift h (𝟙 B) = 𝟙 _ := by
    intro h
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, Category.id_comp]
      apply Over.OverMorphism.ext
      have : Mono (topS Rg).hom := by
        show Mono ((⊤ : (Sp Rg).Opens).ι ≫ 𝟙 _); infer_instance
      apply (cancel_mono (topS Rg).hom).1
      exact (Over.w _).trans (Over.w _).symm
    · rw [Category.assoc, lift_snd, Category.comp_id, Category.id_comp]
  rw [θ, ← Over.comp_left, key]
  rfl

theorem θ_comp_structure {Rg : Type} [CommRing Rg] (B : Over (Sp Rg)) : θ B ≫ fA B = B.hom := by
  rw [θ]; exact Over.w _

end GlobalTheory.HomFixUniv

theorem GlobalTheory.HomFixUniv.hom_of_proport : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (k mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))) (αA : Fin mA → Γ(Sp Rg, ⊤)) (βB : Fin mB → Γ(Sp Rg, ⊤)) (T : Scheme.{0}) (t : T ⟶ Sp Rg) (A' B' : Over T) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Ψ : A'.left ⟶ (topS Rg ⊗ B).left) (c : Fin mA → Fin mB → Γ(T, ⊤)), Hyps L M k bA bB eA eB → (∀ i, GlobalTheory.HomFixUniv.IsVal (eSec A ≫ GlobalTheory.HomFixUniv.θ A) (GlobalTheory.HomFixUniv.uFr A L k eA) (bA i) (αA i)) → (∀ j, GlobalTheory.HomFixUniv.IsVal (eSec B ≫ GlobalTheory.HomFixUniv.θ B) (GlobalTheory.HomFixUniv.uFr B M k eB) (bB j) (βB j)) → IsGrpPullback A' A t φA' → IsGrpPullback B' B t φB' → Ψ ≫ GlobalTheory.HomFixUniv.fA B = A'.hom ≫ t → GlobalTheory.HomFixUniv.Generates bA (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom c → GlobalTheory.HomFixUniv.Proport bA bB (φA' ≫ GlobalTheory.HomFixUniv.θ A) A'.hom Ψ c → GlobalTheory.HomFixUniv.Normal t c αA βB → ∃ Φ : A' ⟶ B', IsMonHom Φ ∧ Φ.left ≫ φB' ≫ GlobalTheory.HomFixUniv.θ B = Ψ := by
  intro Rg _ A B _ _ L M k mA mB bA bB eA eB αA βB T t A' B' _ _ φA' φB' Ψ c hH hvA hvB hA' hB' hΨ hgen hprop hnorm
  obtain ⟨hA, hB, hL, hM, -, -, -, hk, hva, -, hbB⟩ := hH
  have hA'ab : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hA'
  have hB'ab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hB hB'
  have hsnd : (snd (topS Rg) B).left ≫ B.hom = fA B := Over.w (snd (topS Rg) B)
  let Φl : A'.left ⟶ B'.left :=
    hB'.1.lift (Ψ ≫ (snd (topS Rg) B).left) A'.hom (by rw [Category.assoc, hsnd, hΨ])
  have hΦ1 : Φl ≫ φB' = Ψ ≫ (snd (topS Rg) B).left := hB'.1.lift_fst _ _ _
  have hΦ2 : Φl ≫ B'.hom = A'.hom := hB'.1.lift_snd _ _ _
  let Φ : A' ⟶ B' := Over.homMk Φl hΦ2
  have hΨΦ : Φ.left ≫ φB' ≫ θ B = Ψ := by
    show Φl ≫ φB' ≫ θ B = Ψ
    rw [← Category.assoc, hΦ1, Category.assoc, snd_θ, Category.comp_id]
  let e' : T ⟶ A'.left := η[A'].left
  have hEA : e' ≫ φA' = t ≫ eSec A := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hA'
  have hEB : (η[B'].left : T ⟶ B'.left) ≫ φB' = t ≫ eSec B := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left hB'
  have hηA : e' ≫ A'.hom = 𝟙 T := Over.w η[A']
  have heB : eSec B ≫ B.hom = 𝟙 _ := Over.w η[B]
  have hzero : e' ≫ Ψ = t ≫ eSec B ≫ θ B := by
    have hgen' := hgen.pull e'
    have hprop' := hprop.pull e'
    rw [← Category.assoc, hEA, hηA, Category.assoc] at hgen' hprop'
    refine GlobalTheory.T.eq_of_pullbackSectionsProportionalToCombinations Rg _ _ T T (fA B) (LPow A L k (topS Rg)) (LPow B M k (topS Rg)) mA mB bA bB _ (𝟙 T) c _ _
      (GlobalTheory.T.sectionsEmbed_of_baseChangeStableBasis Rg B M k mB bB hB hM hk hva hbB) (LB.isLB_linComb hM _ _) (LB.isLB_linComb hL _ _) hgen' hprop'
      (proport_zero t c hvA hvB hnorm) ?_
    rw [Category.assoc, hΨ, ← Category.assoc, hηA, Category.id_comp, Category.assoc, Category.assoc, θ_comp_structure,
      heB]
    exact (Category.comp_id _).symm
  have hz : η[A'] ≫ Φ = η[B'] := by
    apply Over.OverMorphism.ext
    apply hB'.1.hom_ext
    · show e' ≫ Φl ≫ φB' = _
      rw [hΦ1, ← Category.assoc, hzero, hEB, Category.assoc, Category.assoc, θ_snd, Category.comp_id]
    · exact (Over.w _).trans (Over.w _).symm
  exact ⟨Φ, GlobalTheory.rigidity_holds T A' B' hA'ab hB'ab Φ hz, hΨΦ⟩
