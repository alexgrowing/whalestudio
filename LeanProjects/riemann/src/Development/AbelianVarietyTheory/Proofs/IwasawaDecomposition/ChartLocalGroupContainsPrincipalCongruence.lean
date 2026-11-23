import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartWiden
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatSmulMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincLocStep
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdT.LevQ

theorem princ_in_chart_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {a b T f : ℕ} (h : a = b) (G : Matrix (Fin a) (Fin a) E)
    (hG : G.reindex (finCongr h) (finCongr h) = 1) {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ (G.reindex (finCongr h) (finCongr h)) T f bad) (v : HeightOneSpectrum (𝓞 F))
    (Λ : Submodule (𝓞 E) (Fin a → E)) (hfg : Module.Finite (𝓞 E) (reL h Λ))
    (hsp : Submodule.span E (reL h Λ : Set (Fin b → E)) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ ∀ x : GL (Fin a) (E ⊗[F] v.adicCompletion F), x ∈ levelVL σ G v Λ →
      (∀ y ∈ Formalism.L2.Herm.locL v Λ, ∃ z ∈ Formalism.L2.Herm.locL v Λ,
        (x : Matrix (Fin a) (Fin a) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (n : E ⊗[F] v.adicCompletion F) • z) →
      x ∈ (S.Uloc v).comap (reGL h (E ⊗[F] v.adicCompletion F)).toMonoidHom := by
  subst h
  have hR : ∀ (L : Submodule (𝓞 E) (Fin a → E)), reL rfl L = L := by
    intro L
    ext x
    simp [reL, reV]
  have hGr : G.reindex (finCongr rfl) (finCongr rfl) = G := by
    ext i j; simp
  rw [hR] at hfg hsp
  obtain ⟨M, hM, hMU⟩ := GlobalTheory.Mem.Col2.AdT.Opn.exists_princ_loc_step σ S v hG
  obtain ⟨d, hd, hdA⟩ := GlobalTheory.PrincLat.princ_lat v Λ (Module.Finite.iff_fg.1 hfg) hsp
  refine ⟨M * d, Nat.mul_pos hM hd, fun x hx hpr => ?_⟩
  have hxe : reGL rfl (E ⊗[F] v.adicCompletion F) x = x := by
    apply Units.ext
    ext i j
    simp [reGL]
  show reGL rfl (E ⊗[F] v.adicCompletion F) x ∈ S.Uloc v
  rw [hxe]
  refine hMU x ?_ (hdA M _ hpr)
  have hu : x ∈ UPts σ G (v.adicCompletion F) := hx.1
  rw [hGr]
  exact hu

theorem chart_contains_princ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → (∃ k : Ch → GA B (B.R.N (B.R.m - 1)), I.Reads u a (B.R.m - 1) chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ (Lb0 : Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).sp.X (B.R.m - 1)).rank → (I.rec7 l Z).host.E)), (F u).levJ.Lb = reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 → ∀ β v, v ∈ Q → ∃ n : ℕ, 0 < n ∧ ∀ x, Formalism.L2.Herm.InPrinc (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X (B.R.m - 1)) v n Lb0 x → x ∈ ((K β).lev.Uloc v).comap (reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _).toMonoidHom := by
  intro B X I hOk hPins l Z Ch0 chOf0 F u a Q h1 Ch hCh chOf K g hQ hStd hfr hk hUloc hchi Lb0 hLb β v hv
  have hG := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
  have hfg : Module.Finite (𝓞 (I.rec7 l Z).host.E) (reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0) := by
    rw [← hLb]; exact (F u).levJ.Lb_fin
  have hsp : Submodule.span (I.rec7 l Z).host.E
      (reL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) Lb0 : Set (Fin ((I.rec7 l Z).R.N (B.R.m - 1)) → (I.rec7 l Z).host.E)) = ⊤ := by
    rw [← hLb]; exact (F u).levJ.Lb_span
  obtain ⟨n, hn, hN⟩ := princ_in_chart_gen (sigD (I.rec7 l Z)) (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _))
    ((I.rec7 l Z).sp.X (B.R.m - 1)).gram hG (K β).lev v Lb0 hfg hsp
  exact ⟨n, hn, fun x hx => hN x hx.1 hx.2⟩

end GlobalTheory.Mem.Col2.AdT.LevQ

end
