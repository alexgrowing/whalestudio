import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin Matrix Topology

namespace GlobalTheory.CompanionTheory.CTFin.CapRes

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a b n : ℕ}

theorem map_emb₂ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (e : Fin a ⊕ Fin b ≃ Fin n)
    (g : GL (Fin a) R × GL (Fin b) R) :
    GeneralLinearGroup.map f (GlobalTheory.SmGL.emb₂ R e g) =
      GlobalTheory.SmGL.emb₂ S e (GeneralLinearGroup.map f g.1, GeneralLinearGroup.map f g.2) := by
  apply Units.ext
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  change f ((GlobalTheory.SmGL.emb₂ R e g : Matrix _ _ R) (e p) (e q)) = (GlobalTheory.SmGL.emb₂ S e _ : Matrix _ _ S) (e p) (e q)
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb₂_swap {R : Type} [CommRing R] (e : Fin a ⊕ Fin b ≃ Fin n) (g₁ : GL (Fin a) R) (g₂ : GL (Fin b) R) :
    GlobalTheory.SmGL.emb₂ R ((Equiv.sumComm (Fin b) (Fin a)).trans e) (g₂, g₁) = GlobalTheory.SmGL.emb₂ R e (g₁, g₂) := by
  apply Units.ext
  rw [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.val_emb₂]
  ext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rcases p with p | p <;> rcases q with q | q <;> simp

theorem emb_infGL (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    GlobalTheory.SmGL.emb₂ (Ad E) e (infGL E a y, (1 : GL (Fin b) (Ad E))) =
      infGL E n (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)) := by
  refine ga_ext ?_ ?_
  · rw [pInf_infGL, map_emb₂]; simp
  · rw [pFin_infGL, map_emb₂, pFin_infGL, map_one]
    exact map_one _

def blockL (e : Fin a ⊕ Fin b ≃ Fin n) : Lie E a →L[ℝ] Lie E n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => toL (reindex e e (fromBlocks (Matrix.of x) 0 0 0))
      map_add' := fun x y => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp
      map_smul' := fun c x => by
        funext p q
        obtain ⟨p, rfl⟩ := e.surjective p
        obtain ⟨q, rfl⟩ := e.surjective q
        rcases p with p | p <;> rcases q with q | q <;> simp }

theorem blockL_apply (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) (p q : Fin a ⊕ Fin b) :
    blockL e x (e p) (e q) = fromBlocks (Matrix.of x) 0 0 0 p q := by
  simp [blockL]

def shift (e : Fin a ⊕ Fin b ≃ Fin n) (x : Lie E a) : Lie E n := (oneL E n - blockL e (oneL E a)) + blockL e x

theorem shift_one (e : Fin a ⊕ Fin b ≃ Fin n) : shift e (oneL E a) = oneL E n := by simp [shift]

theorem toL_emb (e : Fin a ⊕ Fin b ≃ Fin n) (y : GL (Fin a) (Cinf E)) :
    toL (GlobalTheory.SmGL.emb₂ (Cinf E) e (y, 1)).val = shift e (toL y.val) := by
  rw [GlobalTheory.SmGL.val_emb₂]
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  simp only [shift, Pi.add_apply, Pi.sub_apply, blockL_apply]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply]

theorem blockL_single (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    blockL e (toL (Matrix.single i j x)) = toL (Matrix.single (e (.inl i)) (e (.inl j)) x) := by
  funext p q
  obtain ⟨p, rfl⟩ := e.surjective p
  obtain ⟨q, rfl⟩ := e.surjective q
  rw [blockL_apply]
  change fromBlocks (Matrix.single i j x) 0 0 0 p q = Matrix.single (e (.inl i)) (e (.inl j)) x (e p) (e q)
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.single_apply]

def iota (e : Fin a ⊕ Fin b ≃ Fin n) : GA E a →* GA E n :=
  (GlobalTheory.SmGL.emb₂ (Ad E) e).comp (MonoidHom.inl _ _)

theorem iota_apply (e : Fin a ⊕ Fin b ≃ Fin n) (m : GA E a) : iota e m = GlobalTheory.SmGL.emb₂ (Ad E) e (m, 1) := rfl

theorem chart_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} {G : GA E a → ℂ} (h : ∀ m, G m = F (iota e m))
    (m : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) : chart G m x = chart F (iota e m) (shift e x) := by
  obtain ⟨u, hu⟩ := id hx
  have e1 : x = toL u.val := hu.symm
  subst e1
  rw [chart_val, h, map_mul, ← toL_emb, chart_val, iota_apply e (infGL E a u), emb_infGL]

theorem lieD_eq (e : Fin a ⊕ Fin b ≃ Fin n) {F : GA E n → ℂ} (hF : F ∈ Sm E n) {G : GA E a → ℂ}
    (h : ∀ m, G m = F (iota e m)) (X : Lie E a) (m : GA E a) :
    lieD X G m = lieD (blockL e X) F (iota e m) := by
  have hd : HasFDerivAt (shift e) (blockL e : Lie E a →L[ℝ] Lie E n) (oneL E a) :=
    (blockL e).hasFDerivAt.const_add _
  have hc : HasFDerivAt (chart F (iota e m)) (fderiv ℝ (chart F (iota e m)) (oneL E n)) (shift e (oneL E a)) := by
    rw [shift_one]; exact (differentiableAt_chart hF _).hasFDerivAt
  have h2 := hc.comp (oneL E a) hd
  have h3 : chart G m =ᶠ[𝓝 (oneL E a)] chart F (iota e m) ∘ shift e := by
    filter_upwards [isOpen_invSet.mem_nhds (show oneL E a ∈ invSet E a from isUnit_one)] with x hx
    exact chart_eq e h m hx
  unfold lieD
  rw [h3.fderiv_eq, h2.fderiv]
  rfl

def relAlg (e : Fin a ⊕ Fin b ≃ Fin n) : Subalgebra ℂ (Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) where
  carrier := {p | ∀ (F : Sm E n) (G : Sm E a), (∀ m, G.1 m = F.1 (iota e m)) →
    ∀ m, (p.1 G).1 m = (p.2 F).1 (iota e m)}
  mul_mem' := fun hp hq F G h m => hp _ _ (hq F G h) m
  add_mem' := fun hp hq F G h m => congrArg₂ (· + ·) (hp F G h m) (hq F G h m)
  algebraMap_mem' := fun c F G h m => congrArg (c • ·) (h m)

theorem lie_mem (e : Fin a ⊕ Fin b ≃ Fin n) (X : Lie E a) :
    ((lie E a X, lie E n (blockL e X)) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  fun F _ h m => lieD_eq e F.2 h X m

theorem lieS_mem (e : Fin a ⊕ Fin b ≃ Fin n) (i j : Fin a) (x : Cinf E) :
    ((lieS E a i j x, lieS E n (e (.inl i)) (e (.inl j)) x) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈
      relAlg e := by
  have := lie_mem e (toL (Matrix.single i j x))
  rwa [blockL_single] at this

theorem Eop_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (i j : Fin a) :
    ((Eop τ i j, Eop τ (e (.inl i)) (e (.inl j))) : Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e :=
  (relAlg e).smul_mem ((relAlg e).sub_mem (lieS_mem e i j _) ((relAlg e).smul_mem (lieS_mem e i j _) _)) _

theorem qdet_mem (e : Fin a ⊕ Fin b ≃ Fin n) (τ : E →+* ℂ) (v : ℂ) :
    ((Formalism.REAL.qdet (Eop τ) v, Formalism.REAL.qdet (fun i j : Fin a => Eop τ (e (.inl i)) (e (.inl j))) v) :
      Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)) ∈ relAlg e := by
  let P := Module.End ℂ (Sm E a) × Module.End ℂ (Sm E n)
  let Z : Fin a → Fin a → P := fun i j => (Eop τ i j, Eop τ (e (.inl i)) (e (.inl j)))
  have h1 := map_qdet (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h2 := map_qdet (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) Z v
  have h3 : Formalism.REAL.qdet Z v ∈ relAlg e := by
    refine (relAlg e).sum_mem fun σ _ => (relAlg e).mul_mem (intCast_mem (relAlg e) _)
      ((relAlg e).list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine (relAlg e).add_mem ?_ (Eop_mem e τ _ _)
    split_ifs
    · exact (relAlg e).algebraMap_mem _
    · exact (relAlg e).zero_mem
  convert h3 using 1
  exact Prod.ext h1.symm h2.symm

theorem aeval_mem (e : Fin a ⊕ Fin b ≃ Fin n) {z : Module.End ℂ (Sm E a)} {z' : Module.End ℂ (Sm E n)}
    (hz : (z, z') ∈ relAlg e) (q : Polynomial ℂ) :
    (Polynomial.aeval z q, Polynomial.aeval z' q) ∈ relAlg e := by
  have h1 := Polynomial.aeval_algHom_apply (AlgHom.fst ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h2 := Polynomial.aeval_algHom_apply (AlgHom.snd ℂ (Module.End ℂ (Sm E a)) (Module.End ℂ (Sm E n))) (z, z') q
  have h3 : Polynomial.aeval (z, z') q ∈ relAlg e := by
    rw [Polynomial.aeval_eq_sum_range]
    exact (relAlg e).sum_mem fun i _ => (relAlg e).smul_mem ((relAlg e).pow_mem hz i) _
  convert h3 using 1
  exact Prod.ext h1 h2

end GlobalTheory.CompanionTheory.CTFin.CapRes

namespace GlobalTheory.CompanionTheory.CTFin

open CapRes

theorem capelli_restrict : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (τ : E →+* ℂ) (u : ℂ) (q : Polynomial ℂ) (F : Sm E (r + s)), (∀ G : Sm E r, (∀ m, G.1 m = F.1 (lev (Ad E) r s (m, 1))) → ∀ m, (Polynomial.aeval (cap (a := r) τ u) q G).1 m = (Polynomial.aeval (capR r s τ u) q F).1 (lev (Ad E) r s (m, 1))) ∧ (∀ G : Sm E s, (∀ m, G.1 m = F.1 (lev (Ad E) r s (1, m))) → ∀ m, (Polynomial.aeval (cap (a := s) τ u) q G).1 m = (Polynomial.aeval (capS r s τ u) q F).1 (lev (Ad E) r s (1, m))) := by
  intro E _ _ _ r s τ u q F
  constructor
  · intro G h m
    exact aeval_mem (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)) (qdet_mem _ τ _) q F G h m
  · intro G h m
    have hι : ∀ m : GA E s, iota ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))) m =
        lev (Ad E) r s (1, m) := fun m => emb₂_swap _ _ _
    have := aeval_mem ((Equiv.sumComm (Fin s) (Fin r)).trans (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))
      (qdet_mem _ τ (u + ((s : ℂ) - 1) / 2)) q F G (fun m => by rw [hι]; exact h m) m
    rw [hι] at this
    exact this

end GlobalTheory.CompanionTheory.CTFin

end
